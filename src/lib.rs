#![allow(dead_code)]
const TICK_DURATION: std::time::Duration = std::time::Duration::from_millis(10);

fn is_timeout(e: std::io::ErrorKind) -> bool{
    e == std::io::ErrorKind::WouldBlock || e == std::io::ErrorKind::TimedOut
}


// enum PacketKind {
//     IP, // complete
// }

#[cfg(test)]
mod tests {
    use super::*;

    use rand::{SeedableRng, Rng, RngCore, CryptoRng};
    use rand_chacha::ChaCha20Rng;
    use rand_pcg::Lcg128CmDxsm64 as SimRng;

    const FAKE_FAIL_RATIO: f64 = 0.1;
    // const FAKE_FAIL_DISTR: rand::distr::Bernoulli = rand::distr::Bernoulli::new(FAKE_FAIL_RATIO).unwrap();

    fn should_fake_fail(rng: &mut SimRng) -> bool {
        // use rand::distr::Distribution;
        if FAKE_FAIL_RATIO == 0.0 {
            false
        } else {
            rng.random_bool(FAKE_FAIL_RATIO)
            // FAKE_FAIL_DISTR.sample(rng)
        }
    }


    fn hook_fail_on_panic() {
        std::panic::set_hook(Box::new(|panic_info| {
            #[allow(clippy::print_stderr)]
            {
                use std::backtrace::*;
                let bt = Backtrace::force_capture();

                eprintln!("\n\n{panic_info}\n");

                // hacky formatting - BacktraceFmt not working for some reason...
                let str = format!("{bt}");
                let splits: Vec<_> = str.split("\n").collect();

                // skip over the internal backtrace unwind steps
                let mut start_i = 0;
                let mut i = 0;
                while i < splits.len() {
                    if splits[i].ends_with("rust_begin_unwind") {
                        i += 1;
                        if i < splits.len() && splits[i].trim().starts_with("at ") {
                            i += 1;
                        }
                        start_i = i;
                    }
                    if splits[i].ends_with("core::panicking::panic_fmt") {
                        i += 1;
                        if i < splits.len() && splits[i].trim().starts_with("at ") {
                            i += 1;
                        }
                        start_i = i;
                        break;
                    }
                    i += 1;
                }

                // print backtrace
                let mut i = start_i;
                let n = 80;
                while i < n {
                    let proc = if let Some(val) = splits.get(i) {
                        val.trim()
                    } else {
                        break;
                    };
                    i += 1;

                    let file_loc = if let Some(val) = splits.get(i) {
                        let val = val.trim();
                        if val.starts_with("at ") {
                            i += 1;
                            val
                        } else {
                            ""
                        }
                    } else {
                        break;
                    };

                    eprintln!(
                        "  {}{}    {}",
                        if i < 20 { " " } else { "" },
                        proc,
                        file_loc
                    );
                }
                if i == n {
                    eprintln!("...");
                }

                std::process::abort();
            }
        }))
    }

    async fn instance(addr_str: &str, peers: &[&str], maybe_seed: Option<u128>) -> std::io::Result<()> {
        hook_fail_on_panic();
        let mut base_rng = {
            let seed : u128 = maybe_seed.unwrap_or_else(||{
                let mut seed_rng = rand::rng();
                ((seed_rng.next_u64() as u128) << 64) | seed_rng.next_u64() as u128
            });
            println!("{} running with seed {:x}", addr_str, seed);
            SimRng::new(seed, 0)
        };

        let (private_key, public_key) = {
            let mut crypto_rng = ChaCha20Rng::seed_from_u64(base_rng.next_u64());
            // NOTE: doing this manually to avoid CryptoRng incompatibilities between different rand_core versions
            let mut secret_key = [0u8; 32];
            crypto_rng.fill_bytes(&mut secret_key);
            let private_key = ed25519_zebra::SigningKey::from(secret_key);
            let public_key = ed25519_zebra::VerificationKeyBytes::from(&private_key);
            (private_key, public_key)
        };

        let sock = std::net::UdpSocket::bind(addr_str)?;
        sock.set_nonblocking(true)?;

        let mut peer_addrs: Vec<core::net::SocketAddr> = Vec::with_capacity(peers.len()+1);

        let my_addr: core::net::SocketAddr = addr_str.parse().unwrap();
        peer_addrs.push(my_addr);
        for peer in peers {
            peer_addrs.push(peer.parse().unwrap());
        }
        println!("{} started with sock: {:?}, peers: {:?}", addr_str, sock, peer_addrs);

        let mut buf = [0; 1024];
        let mut next_tick_time = tokio::time::Instant::now();
        loop {
            tokio::time::sleep_until(next_tick_time).await; // ALT: tokio::time::interval Burst/Skip
            next_tick_time += TICK_DURATION;

            // let (len, addr) = match sock.try_recv_from(&mut buf)
            loop {
                let (len, addr) = match sock.recv_from(&mut buf) {
                    Ok((len, addr)) => if should_fake_fail(&mut base_rng) {
                        println!("{} fake dropped packet {}", addr_str, std::str::from_utf8(&buf[..len]).unwrap());
                        continue;
                    } else {
                        (len, addr)
                    },
                    Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
                    Err(e) => return Err(e),
                };
                let found_peer: core::net::SocketAddr = std::str::from_utf8(&buf[..len]).unwrap().parse().unwrap();
                // println!("{} received {} bytes from {:?}", addr_str, len, addr);
                if !peer_addrs[1..].contains(&found_peer) {
                    println!("{} given new peer {} from {}", addr_str, found_peer, addr);
                    peer_addrs.push(found_peer);
                }
            }

            println!("{} peers: {:?}", addr_str, peer_addrs);

            for dst_peer in &peer_addrs[1..] { // don't  send to ourselves
                for known_peer in &peer_addrs {
                    if dst_peer != known_peer {
                        println!("{} sending {:?} to {:?}", my_addr, known_peer, dst_peer);
                        let len = match sock.send_to(known_peer.to_string().as_bytes(), *dst_peer) {
                            Ok(len) => len,
                            Err(ref e) if is_timeout(e.kind()) => continue,
                            Err(e) => return Err(e),
                        };
                        // println!("{} sent {:?} bytes to {:?}", addr_str, len, dst_peer);
                    }
                }
            }
        }
    }

    #[ignore]
    #[test]
    fn multi_rt() {
        fn init_on_addr(addr_str: &'static str, peers: &'static [&'static str]) -> tokio::task::JoinHandle<()> {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.spawn(async move { instance(addr_str, peers, None).await.expect("no errors") })
        }

        let joins = [
            init_on_addr("127.0.0.1:18080", &[]),
            init_on_addr("127.0.0.1:18081", &["127.0.0.1:18080"]),
            init_on_addr("127.0.0.1:18082", &["127.0.0.1:18080"]),
            init_on_addr("127.0.0.1:18083", &["127.0.0.1:18080"]),
        ];
        loop {
            std::thread::sleep(std::time::Duration::from_secs(1));
        }
    }

    #[test]
    fn single_rt() {
        let rt = tokio::runtime::Runtime::new().unwrap();

        let _joins = [
            rt.spawn(instance("127.0.0.1:18080", &[], None)),
            rt.spawn(instance("127.0.0.1:18081", &["127.0.0.1:18080"], None)),
            rt.spawn(instance("127.0.0.1:18082", &["127.0.0.1:18080"], None)),
            rt.spawn(instance("127.0.0.1:18083", &["127.0.0.1:18080"], None)),
        ];

        rt.block_on(std::future::pending::<()>())
    }
}
