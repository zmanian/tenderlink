#![allow(dead_code)]

use snow::{HandshakeState, StatelessTransportState};
use tokio::time::Instant;
const TICK_DURATION: std::time::Duration = std::time::Duration::from_millis(500);
const TIMEOUT_DURATION: std::time::Duration = std::time::Duration::from_millis(5000);

fn is_timeout(e: std::io::ErrorKind) -> bool{
    e == std::io::ErrorKind::WouldBlock || e == std::io::ErrorKind::TimedOut
}


// enum PacketKind {
//     IP, // complete
// }

#[derive(Debug)]
struct Peer {
    endpoint: SecureUdpEndpoint,
    outgoing_handshake_state: Option<HandshakeState>,
    pending_client_ack_transport_state: Option<StatelessTransportState>,
    transport_state: Option<StatelessTransportState>,
    watch_dog: Instant,
}

#[derive(Clone, Copy)]
struct StaticDHKeyPair {
    private: [u8; 32],
    public: [u8; 32],
}

#[derive(Clone, Copy)]
struct SecureUdpEndpoint {
    public_key: [u8; 32],
    ip_address: [u8; 16],
    port: u16,
}

impl std::fmt::Debug for StaticDHKeyPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "StaticDHKeyPair {{ private: \"")?;
        for b in &self.private {
            write!(f, "{:02x}", b)?;
        }
        write!(f, "\", public: \"")?;
        for b in &self.public {
            write!(f, "{:02x}", b)?;
        }
        write!(f, "\" }}")
    }
}

impl std::fmt::Debug for SecureUdpEndpoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SecureUdpEndpoint {{ public_key: \"")?;
        for b in &self.public_key {
            write!(f, "{:02x}", b)?;
        }
        write!(f, "\", ip_address: \"")?;
        for b in &self.ip_address {
            write!(f, "{:02x}", b)?;
        }
        write!(f, "\", port: {}", self.port)?;
        write!(f, " }}")
    }
}

#[cfg(test)]
mod tests {
    use std::{net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV6}, time::Duration};

    use super::*;

    use rand::{SeedableRng, Rng, RngCore};
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

    async fn instance(my_static_keypair: StaticDHKeyPair, my_endpoint: SecureUdpEndpoint, roster_endpoints: Vec<SecureUdpEndpoint>, maybe_seed: Option<u128>) -> std::io::Result<()> {
        hook_fail_on_panic();
        let mut base_rng = {
            let seed : u128 = maybe_seed.unwrap_or_else(||{
                let mut seed_rng = rand::rng();
                ((seed_rng.next_u64() as u128) << 64) | seed_rng.next_u64() as u128
            });
            println!("{:?} running with seed {:x}", my_endpoint, seed);
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

        let sock = tokio::net::UdpSocket::bind(SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(my_endpoint.ip_address), my_endpoint.port, 0, 0))).await.unwrap();

        let mut peers : Vec<Peer> = roster_endpoints.iter().filter(|e| e.public_key != my_endpoint.public_key).map(|e| {
            Peer { endpoint: e.clone(), outgoing_handshake_state: None, pending_client_ack_transport_state: None, transport_state: None, watch_dog: Instant::now(), }
        }).collect();

        println!("{:?} started with sock: {:?}, peers: {:?}", my_endpoint, sock, peers);

        // Wait for others to start for testing.
        tokio::time::sleep(Duration::from_millis(20)).await;

        let mut recv_buf1 = [0; 2048];
        let mut recv_buf2 = [0; 2048];
        let mut send_buf1 = [0; 2048];
        let mut send_buf2 = [0; 2048];
        let mut next_tick_time = tokio::time::Instant::now();
        loop {
            let was_now = tokio::time::Instant::now();
            if was_now > next_tick_time {
                loop {
                    // TICK CODE
                    for peer in &mut peers {
                        if peer.watch_dog.elapsed() > TIMEOUT_DURATION {
                            peer.outgoing_handshake_state = None;
                            peer.pending_client_ack_transport_state = None;
                            peer.transport_state = None;
                            peer.watch_dog = Instant::now();
                        }

                        if let Some(transport) = &mut peer.transport_state {
                            // NONCE SHOULD NOT BE ZERO
                            let length = transport.write_message(0, b"BEAT", &mut send_buf2).unwrap();
                            match sock.try_send_to(&send_buf2[0..length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer.endpoint.ip_address), peer.endpoint.port, 0, 0))) {
                                Ok(_) => (),
                                Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                Err(error) => println!("Socket error: {:?}", error),
                            }
                        }
                    }
                    for peer in &mut peers {
                        if peer.transport_state.is_none() && peer.outgoing_handshake_state.is_none() && peer.pending_client_ack_transport_state.is_none() {
                            let mut outgoing_state = snow::Builder::new("Noise_IK_25519_ChaChaPoly_BLAKE2s".parse().unwrap())
                                .local_private_key(&my_static_keypair.private).unwrap()
                                .remote_public_key(&peer.endpoint.public_key).unwrap()
                                .build_initiator().unwrap();
                            let length = outgoing_state.write_message(b"CLIENT HELLO", &mut send_buf2).unwrap();
                            match sock.try_send_to(&send_buf2[0..length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer.endpoint.ip_address), peer.endpoint.port, 0, 0))) {
                                Ok(_) => (),
                                Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                Err(error) => println!("Socket error: {:?}", error),
                            }
                            peer.outgoing_handshake_state = Some(outgoing_state);
                        }
                    }
                    break;
                }
                let now_now = tokio::time::Instant::now();
                if now_now - next_tick_time > TICK_DURATION {
                    next_tick_time = now_now + TICK_DURATION;
                } else {
                    next_tick_time += TICK_DURATION;
                }
            }

            let remaining = next_tick_time.saturating_duration_since(was_now);
            let (length, addr) = match tokio::time::timeout(remaining, sock.recv_from(&mut recv_buf1)).await {
                Err(_elapsed) => continue, // timeout
                Ok(Err(error)) => { println!("Socket error: {:?}", error); continue; },
                Ok(Ok(ret)) => if should_fake_fail(&mut base_rng) { continue; } else { ret },
            };
            let raw_msg = &recv_buf1[0..length];

            let from_ip = match addr {
                SocketAddr::V4(v4) => v4.ip().to_ipv6_mapped().octets(),
                SocketAddr::V6(v6) => v6.ip().octets(),
            };
            let from_port = addr.port();

            // DECRYPT
            let mut msg = None;
            if let Some(i) = peers.iter().position(|p| p.endpoint.ip_address == from_ip && p.endpoint.port == from_port) {
                loop {
                    let peer = &mut peers[i];
                    if let Some(transport) = &mut peer.transport_state {
                        // NONCE SHOULD NOT BE ZERO
                        if let Ok(length) = transport.read_message(0, raw_msg, &mut recv_buf2) {
                            msg = Some(&recv_buf2[0..length]);
                            peer.watch_dog = Instant::now(); // TODO reset on acknowledged heartbeat
                            break;
                        }
                    }
                    if let Some(outgoing) = &mut peer.outgoing_handshake_state {
                        if let Ok(length) = outgoing.read_message(raw_msg, &mut recv_buf2) {
                            let local_msg = &recv_buf2[0..length];
                            if local_msg == b"SERVER HELLO" {
                                // TODO hash
                                if peer.pending_client_ack_transport_state.is_none() || my_endpoint.port > peer.endpoint.port {
                                    if let Ok(transport) = peer.outgoing_handshake_state.take().unwrap().into_stateless_transport_mode() {
                                        println!("{}: Finished outgoing handshake with {}", my_endpoint.port, addr);

                                        // NONCE SHOULD NOT BE ZERO
                                        let length = transport.write_message(0, b"CLIENT ACK", &mut send_buf2).unwrap();
                                        match sock.try_send_to(&send_buf2[0..length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer.endpoint.ip_address), peer.endpoint.port, 0, 0))) {
                                            Ok(_) => (),
                                            Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                            Err(error) => println!("Socket error: {:?}", error),
                                        }
                                        
                                        peer.transport_state = Some(transport);
                                        peer.outgoing_handshake_state = None;
                                        peer.pending_client_ack_transport_state = None;
                                    }
                                    break;
                                }
                            }
                        }
                    }
                    if let Some(incoming) = &mut peer.pending_client_ack_transport_state {
                        // NONCE SHOULD NOT BE ZERO
                        if let Ok(length) = incoming.read_message(0, raw_msg, &mut recv_buf2) {
                            let local_msg = &recv_buf2[0..length];
                            if local_msg == b"CLIENT ACK" {
                                println!("{}: Finished incoming handshake with {}", my_endpoint.port, addr);
                                peer.transport_state = peer.pending_client_ack_transport_state.take();
                                peer.outgoing_handshake_state = None;
                                break;
                            }
                        }
                    }
                    let mut incoming_state = snow::Builder::new("Noise_IK_25519_ChaChaPoly_BLAKE2s".parse().unwrap())
                        .local_private_key(&my_static_keypair.private).unwrap()
                        .build_responder().unwrap();
                    if let Ok(length) = incoming_state.read_message(raw_msg, &mut recv_buf2) {
                        let local_msg = &recv_buf2[0..length];
                        if local_msg == b"CLIENT HELLO" {
                            // TODO hash
                            if peer.outgoing_handshake_state.is_none() || my_endpoint.port <= peer.endpoint.port {
                                let length = incoming_state.write_message(b"SERVER HELLO", &mut send_buf2).unwrap();
                                match sock.try_send_to(&send_buf2[0..length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer.endpoint.ip_address), peer.endpoint.port, 0, 0))) {
                                    Ok(_) => (),
                                    Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                    Err(error) => println!("Socket error: {:?}", error),
                                }
                                if let Ok(transport) = incoming_state.into_stateless_transport_mode() {
                                    peer.pending_client_ack_transport_state = Some(transport);
                                }
                                break;
                            }
                        }
                    }
                    break;
                }
            } else {
                println!("UNKNOWN PEER CONNECTED. NOT IMPLEMENTED YET.");
                continue;
            }
            if msg.is_none() { continue; }
            let msg = msg.unwrap();

            // HANDLE UDP PACKET
            println!("{}: Got '{:?}' from {}", my_endpoint.port, msg, addr);
        }
    }

    // #[ignore]
    // #[test]
    // fn multi_rt() {
    //     fn init_on_addr(addr_str: &'static str, peers: &'static [&'static str]) -> tokio::task::JoinHandle<()> {
    //         let rt = tokio::runtime::Runtime::new().unwrap();
    //         rt.spawn(async move { instance(addr_str, peers, None).await.expect("no errors") })
    //     }

    //     let joins = [
    //         init_on_addr("127.0.0.1:18080", &[]),
    //         init_on_addr("127.0.0.1:18081", &["127.0.0.1:18080"]),
    //         init_on_addr("127.0.0.1:18082", &["127.0.0.1:18080"]),
    //         init_on_addr("127.0.0.1:18083", &["127.0.0.1:18080"]),
    //     ];
    //     loop {
    //         std::thread::sleep(std::time::Duration::from_secs(1));
    //     }
    // }

    #[test]
    fn single_rt() {
        let rt = tokio::runtime::Runtime::new().unwrap();

        let static_keypairs : Vec<StaticDHKeyPair> = (0..4).map(|_| {
            let kp = snow::Builder::new("Noise_IK_25519_ChaChaPoly_BLAKE2s".parse().unwrap()).generate_keypair().unwrap();
            StaticDHKeyPair { private: kp.private.try_into().unwrap(), public: kp.public.try_into().unwrap(), }
        }).collect();
        let endpoints : Vec<SecureUdpEndpoint> = static_keypairs.iter().enumerate().map(|(i, skp)| {
            let ip = "127.0.0.1".parse::<Ipv4Addr>().unwrap().to_ipv6_mapped();
            let port : u16 = 18080 + i as u16;
            SecureUdpEndpoint { ip_address: ip.octets(), port, public_key: skp.public }
        }).collect();

        let _joins = [
            rt.spawn(instance(static_keypairs[0], endpoints[0], endpoints.clone(), None)),
            rt.spawn(instance(static_keypairs[1], endpoints[1], endpoints.clone(), None)),
            rt.spawn(instance(static_keypairs[2], endpoints[2], endpoints.clone(), None)),
            rt.spawn(instance(static_keypairs[3], endpoints[3], endpoints.clone(), None)),
        ];

        rt.block_on(std::future::pending::<()>())
    }
}
