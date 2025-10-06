#![allow(dead_code)]


use std::{io::{Cursor, Read, Write}, net::{Ipv6Addr, SocketAddr, SocketAddrV6}, time::Duration};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use ed25519_zebra::{SigningKey, VerificationKeyBytes};
use rand::{seq::IndexedRandom, Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use rand_pcg::Lcg128CmDxsm64 as SimRng;
use snow::{HandshakeState, StatelessTransportState};
use tokio::time::Instant;

const TICK_DURATION: std::time::Duration = std::time::Duration::from_millis(200);
const TIMEOUT_DURATION: std::time::Duration = std::time::Duration::from_millis(5000);
const NONCE_FORWARD_JUMP_TOLERANCE: u64 = 512;

const FAKE_FAIL_RATIO: f64 = 0.9;
// const FAKE_FAIL_DISTR: rand::distr::Bernoulli = rand::distr::Bernoulli::new(FAKE_FAIL_RATIO).unwrap();

fn should_fake_fail(rng: &mut SimRng) -> bool {
    if std::time::SystemTime::UNIX_EPOCH.elapsed().unwrap().as_secs() / 10 % 2 == 0 {
        return false;
    }
    // use rand::distr::Distribution;
    if FAKE_FAIL_RATIO == 0.0 {
        false
    } else {
        rng.random_bool(FAKE_FAIL_RATIO)
        // FAKE_FAIL_DISTR.sample(rng)
    }
}

fn is_timeout(e: std::io::ErrorKind) -> bool{
    e == std::io::ErrorKind::WouldBlock || e == std::io::ErrorKind::TimedOut
}

// enum PacketKind {
//     IP, // complete
// }

#[derive(Debug)]
struct Peer {
    root_public_key: [u8; 32],
    endpoint: Option<SecureUdpEndpoint>,
    outgoing_handshake_state: Option<HandshakeState>,
    pending_client_ack_transport_state: Option<StatelessTransportState>,
    transport_state: Option<StatelessTransportState>,
    watch_dog: Instant,

    nonce_ack_latest: u64,
    nonce_ack_field: u64,
    on_send_next_nonce: u64,

    connection_is_unknown: bool,
}
impl Default for Peer {
    fn default() -> Peer {
        Peer {
            root_public_key: [0_u8; 32],
            endpoint: None,
            outgoing_handshake_state: None,
            pending_client_ack_transport_state: None,
            transport_state: None,
            watch_dog: Instant::now(),

            nonce_ack_latest: 0,
            nonce_ack_field: 0,
            on_send_next_nonce: 0,

            connection_is_unknown: false,
        }
    }
}

#[derive(Debug)]
struct UnknownPeer {
    endpoint: SecureUdpEndpoint,
    transport_state: StatelessTransportState,
    pending_client_ack: bool,
    watch_dog: Instant,

    nonce_ack_latest: u64,
    nonce_ack_field: u64,
    on_send_next_nonce: u64,
}

#[derive(Clone, Copy)]
struct StaticDHKeyPair {
    private: [u8; 32],
    public: [u8; 32],
}

#[derive(PartialEq, Eq, Clone, Copy)]
struct SecureUdpEndpoint {
    public_key: [u8; 32],
    ip_address: [u8; 16],
    port: u16,
}
impl Default for SecureUdpEndpoint {
    fn default() -> SecureUdpEndpoint {
        SecureUdpEndpoint { public_key: [0_u8; 32], ip_address: [0_u8; 16], port: 0 }
    }
}
impl SecureUdpEndpoint {
    pub fn write_to<W: Write>(&self, mut w: W) -> std::io::Result<()> {
        w.write_all(&self.public_key)?;
        w.write_all(&self.ip_address)?;
        w.write_u16::<LittleEndian>(self.port)?;
        Ok(())
    }

    pub fn read_from<R: Read>(mut r: R) -> std::io::Result<Self> {
        let mut endpoint = SecureUdpEndpoint::default();
        r.read_exact(&mut endpoint.public_key)?;
        r.read_exact(&mut endpoint.ip_address)?;
        endpoint.port = r.read_u16::<LittleEndian>()?;
        Ok(endpoint)
    }
}

#[derive(Debug, Clone, Copy)]
struct EndpointEvidence {
    endpoint: SecureUdpEndpoint,
    root_public_key: [u8; 32],
}
impl Default for EndpointEvidence {
    fn default() -> EndpointEvidence {
        EndpointEvidence { endpoint: SecureUdpEndpoint::default(), root_public_key: [0_u8; 32] }
    }
}
impl EndpointEvidence {
    pub fn write_to<W: Write>(&self, mut w: W) -> std::io::Result<()> {
        self.endpoint.write_to(&mut w)?;
        w.write_all(self.root_public_key.as_ref())?;
        Ok(())
    }

    pub fn read_from<R: Read>(mut r: R) -> std::io::Result<Self> {
        let endpoint = SecureUdpEndpoint::read_from(&mut r)?;
        let mut key_bytes = [0_u8; 32];
        r.read_exact(&mut key_bytes)?;
        Ok(EndpointEvidence { endpoint, root_public_key: key_bytes })
    }
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

async fn instance(my_root_private_key: SigningKey, my_static_keypair: Option<StaticDHKeyPair>, my_endpoint: Option<SecureUdpEndpoint>, roster: Vec<[u8; 32]>, mut roster_endpoint_evidence: Vec<EndpointEvidence>, maybe_seed: Option<u128>) -> std::io::Result<()> {
    hook_fail_on_panic();
    let mut base_rng = {
        let seed : u128 = maybe_seed.unwrap_or_else(||{
            let mut seed_rng = rand::rng();
            ((seed_rng.next_u64() as u128) << 64) | seed_rng.next_u64() as u128
        });
        SimRng::new(seed, 0)
    };

    let my_root_public_key = VerificationKeyBytes::from(&my_root_private_key);
    let my_static_keypair = my_static_keypair.unwrap_or_else(|| {
        let kp = snow::Builder::new("Noise_IK_25519_ChaChaPoly_BLAKE2s".parse().unwrap()).generate_keypair().unwrap();
        StaticDHKeyPair { private: kp.private.try_into().unwrap(), public: kp.public.try_into().unwrap(), }
    });

    let sock = tokio::net::UdpSocket::bind(SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::UNSPECIFIED, my_endpoint.map(|e|e.port).unwrap_or(0), 0, 0))).await.unwrap();
    let my_port = sock.local_addr().unwrap().port();
    
    let mut peers : Vec<Peer> = roster.iter().filter(|k| **k != my_root_public_key.as_ref()).map(|k| {
        let mut p = Peer::default();
        p.root_public_key = *k;
        p
    }).collect();
    
    for evidence in &roster_endpoint_evidence {
        if let Some(i) = peers.iter().position(|p| p.root_public_key == evidence.root_public_key) {
            peers[i].endpoint = Some(evidence.endpoint);
        }
    }
    println!("socket port={}, peers endpoints={:?}", my_port, peers.iter().map(|p|p.endpoint).collect::<Vec<_>>());

    let mut my_endpoint_evidence = if let Some(i) = roster_endpoint_evidence.iter().position(|e| &e.root_public_key == my_root_public_key.as_ref()) {
        Some(roster_endpoint_evidence[i])
    } else {
        if let Some(endpoint) = my_endpoint {
            Some(EndpointEvidence { endpoint: endpoint, root_public_key: my_root_public_key.into() })
        } else { None }
    };

    // Wait for others to start for testing.
    tokio::time::sleep(Duration::from_millis(20)).await;

    let mut unknown_peers: Vec<UnknownPeer> = Vec::new();

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
                unknown_peers.retain(|peer| {
                    if peer.watch_dog.elapsed() > TIMEOUT_DURATION {
                        println!("{}: Disconnected from unknown peer {:?}", my_port, peer.endpoint);
                        false
                    } else { true }
                });
                for peer in &mut peers {
                    if peer.watch_dog.elapsed() > TIMEOUT_DURATION {
                        if peer.transport_state.is_some() {
                            println!("{}: Disconnected from peer {:?}", my_port, peer.endpoint);
                        }
                        peer.outgoing_handshake_state = None;
                        peer.pending_client_ack_transport_state = None;
                        peer.transport_state = None;
                        peer.watch_dog = Instant::now();
                    }

                    if let Some(peer_endpoint) = peer.endpoint {
                        if let Some(transport) = &mut peer.transport_state {
                            if peer.connection_is_unknown {
                                // Gossip evidence in order to trigger upgrade
                                if let Some(evidence) = my_endpoint_evidence {
                                    let mut c = Cursor::new(&mut send_buf1[..]);
                                    c.write_all(b"ENDPOINT EVIDENCE").unwrap();
                                    evidence.write_to(&mut c).unwrap();
                                    let len1 = c.position() as usize;
                                    let length = transport.write_message(peer.on_send_next_nonce, &send_buf1[..len1], &mut send_buf2[8..]).unwrap();
                                    send_buf2[0..8].copy_from_slice(&peer.on_send_next_nonce.to_le_bytes());
                                    peer.on_send_next_nonce += 1;
                                    match sock.try_send_to(&send_buf2[0..8+length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer_endpoint.ip_address), peer_endpoint.port, 0, 0))) {
                                        Ok(_) => (),
                                        Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                        Err(error) => println!("Socket error: {:?}", error),
                                    }
                                }
                            }
                            else {
                                let length = transport.write_message(peer.on_send_next_nonce, b"BEAT", &mut send_buf2[8..]).unwrap();
                                send_buf2[0..8].copy_from_slice(&peer.on_send_next_nonce.to_le_bytes());
                                peer.on_send_next_nonce += 1;
                                match sock.try_send_to(&send_buf2[0..8+length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer_endpoint.ip_address), peer_endpoint.port, 0, 0))) {
                                    Ok(_) => (),
                                    Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                    Err(error) => println!("Socket error: {:?}", error),
                                }
                            }
                        }
                    }
                }
                for peer in &mut peers {
                    if let Some(peer_endpoint) = peer.endpoint {
                        if peer.transport_state.is_none() && peer.outgoing_handshake_state.is_none() && peer.pending_client_ack_transport_state.is_none() {
                            let mut outgoing_state = snow::Builder::new("Noise_IK_25519_ChaChaPoly_BLAKE2s".parse().unwrap())
                                .local_private_key(&my_static_keypair.private).unwrap()
                                .remote_public_key(&peer_endpoint.public_key).unwrap()
                                .build_initiator().unwrap();
                            let length = outgoing_state.write_message(b"CLIENT HELLO", &mut send_buf2).unwrap();
                            match sock.try_send_to(&send_buf2[0..length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer_endpoint.ip_address), peer_endpoint.port, 0, 0))) {
                                Ok(_) => (),
                                Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                Err(error) => println!("Socket error: {:?}", error),
                            }
                            peer.outgoing_handshake_state = Some(outgoing_state);
                        }

                        if let Some(transport) = &mut peer.transport_state {
                            if let Some(evidence) = roster_endpoint_evidence.choose(&mut base_rng) {
                                let mut c = Cursor::new(&mut send_buf1[..]);
                                c.write_all(b"ENDPOINT EVIDENCE").unwrap();
                                evidence.write_to(&mut c).unwrap();
                                let len1 = c.position() as usize;
                                let length = transport.write_message(peer.on_send_next_nonce, &send_buf1[..len1], &mut send_buf2[8..]).unwrap();
                                send_buf2[0..8].copy_from_slice(&peer.on_send_next_nonce.to_le_bytes());
                                peer.on_send_next_nonce += 1;
                                match sock.try_send_to(&send_buf2[0..8+length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer_endpoint.ip_address), peer_endpoint.port, 0, 0))) {
                                    Ok(_) => (),
                                    Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                    Err(error) => println!("Socket error: {:?}", error),
                                }
                            }
                        }
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
        if length < 8 { continue; } // early out to simplify nonce code
        let raw_msg = &recv_buf1[0..length];

        let from_ip = match addr {
            SocketAddr::V4(v4) => v4.ip().to_ipv6_mapped().octets(),
            SocketAddr::V6(v6) => v6.ip().octets(),
        };
        let from_port = addr.port();

        // DECRYPT
        let mut peer_index = 0;
        let mut peer_is_unknown = false;
        let mut nonce = 0;
        let mut msg = None;

        //  NOTE(Security): Actually we would need to loop because a peer could sign a message claiming to own an IP and PORT that it actually does not own. That also means falling back on
        //      the unknown connections array since that also shouldn't be able to be blocked.
        if let Some(i) = peers.iter().map(|p| p.endpoint.unwrap_or_default()).position(|endpoint| endpoint.ip_address == from_ip && endpoint.port == from_port) {
            let peer_endpoint = peers[i].endpoint.unwrap();
            loop {
                let peer = &mut peers[i];
                if let Some(transport) = &mut peer.transport_state {
                    nonce = u64::from_le_bytes(raw_msg[0..8].try_into().unwrap());
                    if let Ok(length) = transport.read_message(nonce, &raw_msg[8..], &mut recv_buf2) {
                        let mut reject = false;
                        if nonce > peer.nonce_ack_latest && nonce > peer.nonce_ack_latest + NONCE_FORWARD_JUMP_TOLERANCE { reject = true; }
                        if nonce == peer.nonce_ack_latest { reject = true; }
                        if nonce + 64 < peer.nonce_ack_latest { reject = true; }
                        if nonce < peer.nonce_ack_latest && 1_u64 << (peer.nonce_ack_latest - nonce) & peer.nonce_ack_field != 0 { reject = true; }
                        if reject == false {
                            msg = Some(&recv_buf2[0..length]);
                            peer_index = i;
                        }
                        break;
                    }
                }
                if let Some(outgoing) = &mut peer.outgoing_handshake_state {
                    if let Ok(length) = outgoing.read_message(raw_msg, &mut recv_buf2) {
                        if length >= 8 {
                            nonce = u64::from_le_bytes(recv_buf2[0..8].try_into().unwrap());
                            let local_msg = &recv_buf2[8..length];
                            if local_msg == b"SERVER HELLO" {
                                // TODO hash
                                if peer.pending_client_ack_transport_state.is_none() || my_port > peer_endpoint.port {
                                    if let Ok(transport) = peer.outgoing_handshake_state.take().unwrap().into_stateless_transport_mode() {
                                        println!("{}: Finished outgoing handshake and got nonce {} with {}", my_port, nonce, addr);

                                        let start_nonce  = rand::random::<u64>() >> 1;
                                        let length = transport.write_message(start_nonce, b"CLIENT ACK", &mut send_buf2[8..]).unwrap();
                                        send_buf2[0..8].copy_from_slice(&start_nonce.to_le_bytes());
                                        match sock.try_send_to(&send_buf2[0..8+length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer_endpoint.ip_address), peer_endpoint.port, 0, 0))) {
                                            Ok(_) => (),
                                            Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                            Err(error) => println!("Socket error: {:?}", error),
                                        }
                                        
                                        peer.transport_state = Some(transport);
                                        peer.outgoing_handshake_state = None;
                                        peer.pending_client_ack_transport_state = None;
                                        peer.nonce_ack_latest = nonce;
                                        peer.nonce_ack_field = !0;
                                        peer.connection_is_unknown = false;
                                        peer.on_send_next_nonce = start_nonce + 1;
                                    }
                                    break;
                                }
                            }
                            if local_msg.len() == b"SERVER UNKNOWN HELLO".len() + 18 && &local_msg[0..b"SERVER UNKNOWN HELLO".len()] == b"SERVER UNKNOWN HELLO" {
                                let other_side_ip = &local_msg[b"SERVER UNKNOWN HELLO".len()..b"SERVER UNKNOWN HELLO".len()+16];
                                let other_side_port = &local_msg[b"SERVER UNKNOWN HELLO".len()+16..b"SERVER UNKNOWN HELLO".len()+18];
                                let other_side_endpoint = SecureUdpEndpoint { ip_address: other_side_ip.try_into().unwrap(), port: u16::from_le_bytes(other_side_port.try_into().unwrap()), public_key: my_static_keypair.public };
                                // TODO hash
                                if let Ok(transport) = peer.outgoing_handshake_state.take().unwrap().into_stateless_transport_mode() {
                                    println!("{}: Finished outgoing unknown handshake and got nonce {} with {}, I am percieved as {:?}", my_port, nonce, addr, other_side_endpoint);

                                    if my_endpoint_evidence.is_none() {
                                        let evidence = EndpointEvidence { endpoint: other_side_endpoint, root_public_key: my_root_public_key.into() };
                                        println!("{}: I am locking in the endpoint evidence {:?}", my_port, evidence);
                                        my_endpoint_evidence = Some(evidence);
                                    }

                                    let start_nonce  = rand::random::<u64>() >> 1;
                                    let length = transport.write_message(start_nonce, b"CLIENT UNKNOWN ACK", &mut send_buf2[8..]).unwrap();
                                    send_buf2[0..8].copy_from_slice(&start_nonce.to_le_bytes());
                                    match sock.try_send_to(&send_buf2[0..8+length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer_endpoint.ip_address), peer_endpoint.port, 0, 0))) {
                                        Ok(_) => (),
                                        Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                        Err(error) => println!("Socket error: {:?}", error),
                                    }
                                    
                                    peer.transport_state = Some(transport);
                                    peer.outgoing_handshake_state = None;
                                    peer.pending_client_ack_transport_state = None;
                                    peer.nonce_ack_latest = nonce;
                                    peer.nonce_ack_field = !0;
                                    peer.connection_is_unknown = true;
                                    peer.on_send_next_nonce = start_nonce + 1;
                                }
                                break;
                            }
                        }
                    }
                }
                if let Some(incoming) = &mut peer.pending_client_ack_transport_state {
                    nonce = u64::from_le_bytes(raw_msg[0..8].try_into().unwrap());
                    if let Ok(length) = incoming.read_message(nonce, &raw_msg[8..], &mut recv_buf2) {
                        let local_msg = &recv_buf2[0..length];
                        if local_msg == b"CLIENT ACK" {
                            println!("{}: Finished incoming handshake and got nonce {} with {}", my_port, nonce, addr);
                            peer.transport_state = peer.pending_client_ack_transport_state.take();
                            peer.outgoing_handshake_state = None;
                            peer.nonce_ack_latest = nonce;
                            peer.nonce_ack_field = !0;
                            peer.connection_is_unknown = false;
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
                        let client_endpoint = SecureUdpEndpoint { public_key: incoming_state.get_remote_static().unwrap().try_into().unwrap(), ip_address: from_ip, port: from_port };
                        println!("{}: Server recieved client hello from static key = {:?}", my_port, client_endpoint);
                        // TODO hash
                        if peer.outgoing_handshake_state.is_none() || my_port <= peer_endpoint.port {
                            let hello_bytes = b"SERVER HELLO";
                            let start_nonce  = rand::random::<u64>() >> 1;
                            send_buf1[0..8].copy_from_slice(&u64::to_le_bytes(start_nonce));
                            send_buf1[8..8+hello_bytes.len()].copy_from_slice(hello_bytes);
                            let length = incoming_state.write_message(&send_buf1[0..8+hello_bytes.len()], &mut send_buf2).unwrap();
                            match sock.try_send_to(&send_buf2[0..length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer_endpoint.ip_address), peer_endpoint.port, 0, 0))) {
                                Ok(_) => (),
                                Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                Err(error) => println!("Socket error: {:?}", error),
                            }
                            if let Ok(transport) = incoming_state.into_stateless_transport_mode() {
                                peer.pending_client_ack_transport_state = Some(transport);
                                peer.on_send_next_nonce = start_nonce+1;
                            }
                            break;
                        }
                    }
                }
                break;
            }
        } else {
            loop {
                if let Some(i) = unknown_peers.iter().position(|p| p.endpoint.ip_address == from_ip && p.endpoint.port == from_port) {
                    let peer = &mut unknown_peers[i];
                    nonce = u64::from_le_bytes(raw_msg[0..8].try_into().unwrap());
                    if let Ok(length) = peer.transport_state.read_message(nonce, &raw_msg[8..], &mut recv_buf2) {
                        let local_msg = &recv_buf2[0..length];
                        if peer.pending_client_ack {
                            if local_msg == b"CLIENT UNKNOWN ACK" {
                                println!("{}: Finished incoming unknown handshake and got nonce {} with {}", my_port, nonce, addr);
                                peer.pending_client_ack = false;
                                peer.nonce_ack_latest = nonce;
                                peer.nonce_ack_field = !0;
                                break;
                            }
                            break;
                        }
                        let mut reject = false;
                        if nonce > peer.nonce_ack_latest && nonce > peer.nonce_ack_latest + NONCE_FORWARD_JUMP_TOLERANCE { reject = true; }
                        if nonce == peer.nonce_ack_latest { reject = true; }
                        if nonce + 64 < peer.nonce_ack_latest { reject = true; }
                        if nonce < peer.nonce_ack_latest && 1_u64 << (peer.nonce_ack_latest - nonce) & peer.nonce_ack_field != 0 { reject = true; }
                        if reject == false {
                            msg = Some(&recv_buf2[0..length]);
                            peer_index = i;
                            peer_is_unknown = true;
                        }
                        break;
                    }
                }
                let mut incoming_state = snow::Builder::new("Noise_IK_25519_ChaChaPoly_BLAKE2s".parse().unwrap())
                    .local_private_key(&my_static_keypair.private).unwrap()
                    .build_responder().unwrap();
                if let Ok(length) = incoming_state.read_message(raw_msg, &mut recv_buf2) {
                    let local_msg = &recv_buf2[0..length];
                    if local_msg == b"CLIENT HELLO" {
                        let client_endpoint = SecureUdpEndpoint { public_key: incoming_state.get_remote_static().unwrap().try_into().unwrap(), ip_address: from_ip, port: from_port };
                        println!("{}: Server recieved client hello from unknown peer with static key = {:?}", my_port, client_endpoint);
                        
                        let hello_bytes = b"SERVER UNKNOWN HELLO";
                        let start_nonce  = rand::random::<u64>() >> 1;
                        send_buf1[0..8].copy_from_slice(&u64::to_le_bytes(start_nonce));
                        send_buf1[8..8+hello_bytes.len()].copy_from_slice(hello_bytes);
                        send_buf1[8+hello_bytes.len()..8+hello_bytes.len()+16].copy_from_slice(&from_ip);
                        send_buf1[8+hello_bytes.len()+16..8+hello_bytes.len()+16+2].copy_from_slice(&from_port.to_le_bytes());
                        let length = incoming_state.write_message(&send_buf1[0..8+hello_bytes.len()+16+2], &mut send_buf2).unwrap();
                        match sock.try_send_to(&send_buf2[0..length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(client_endpoint.ip_address), client_endpoint.port, 0, 0))) {
                            Ok(_) => (),
                            Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                            Err(error) => println!("Socket error: {:?}", error),
                        }
                        if let Ok(transport) = incoming_state.into_stateless_transport_mode() {
                            unknown_peers.push(UnknownPeer { endpoint: client_endpoint, transport_state: transport, pending_client_ack: true, watch_dog: Instant::now(), nonce_ack_latest: 0, nonce_ack_field: 0, on_send_next_nonce: start_nonce+1, });
                        }
                        break;
                    }
                }
                break;
            }
        }
        if msg.is_none() { continue; }
        let msg = msg.unwrap();

        if peer_is_unknown {
            let peer = &mut unknown_peers[peer_index];
            peer.watch_dog = Instant::now();

            // Update nonce tracking
            if nonce > peer.nonce_ack_latest {
                peer.nonce_ack_latest += 1;
                peer.nonce_ack_field <<= 1;
                peer.nonce_ack_field |= 1;
                let shift_amount = nonce - peer.nonce_ack_latest;
                if shift_amount >= 64 {
                    peer.nonce_ack_field = 0;
                } else if shift_amount != 0 {
                    peer.nonce_ack_field <<= shift_amount;
                    peer.nonce_ack_latest = nonce;
                }
            } else {
                peer.nonce_ack_field |= 1_u64 << (peer.nonce_ack_latest - nonce);
            }

            if &msg[0..b"ENDPOINT EVIDENCE".len()] == b"ENDPOINT EVIDENCE" {
                let evidence = EndpointEvidence::read_from(&msg[b"ENDPOINT EVIDENCE".len()..]).unwrap();

                if let Some(i) = peers.iter().position(|p| p.root_public_key == evidence.root_public_key) {
                    peers[i].endpoint = Some(evidence.endpoint);
                    if peer.endpoint == evidence.endpoint {
                        println!("{}: Promoting unknown peer connection {:?}", my_port, peer.endpoint);
                        let peer = unknown_peers.remove(peer_index);
                        peers[i].outgoing_handshake_state = None;
                        peers[i].pending_client_ack_transport_state = None;
                        peers[i].transport_state = Some(peer.transport_state);
                        peers[i].watch_dog = Instant::now();
                        peers[i].nonce_ack_latest = peer.nonce_ack_latest;
                        peers[i].nonce_ack_field = peer.nonce_ack_field;
                        peers[i].on_send_next_nonce = peer.on_send_next_nonce;
                        peers[i].connection_is_unknown = false;
                    }
                    roster_endpoint_evidence.retain(|e| e.root_public_key != evidence.root_public_key);
                    roster_endpoint_evidence.push(evidence);
                }
                continue;
            } else {
                println!("{}:  From unknown peer!   field={:016X} Got '{:?}' from {}", my_port, peer.nonce_ack_field, msg, addr);
            }
        }
        else {
            let peer = &mut peers[peer_index];
            peer.watch_dog = Instant::now();
    
            // Update nonce tracking
            if nonce > peer.nonce_ack_latest {
                peer.nonce_ack_latest += 1;
                peer.nonce_ack_field <<= 1;
                peer.nonce_ack_field |= 1;
                let shift_amount = nonce - peer.nonce_ack_latest;
                if shift_amount >= 64 {
                    peer.nonce_ack_field = 0;
                } else if shift_amount != 0 {
                    peer.nonce_ack_field <<= shift_amount;
                    peer.nonce_ack_latest = nonce;
                }
            } else {
                peer.nonce_ack_field |= 1_u64 << (peer.nonce_ack_latest - nonce);
            }

            if peer.connection_is_unknown {
                if msg == b"BEAT" {
                    println!("{}: Got a heartbeat, this means that the other side does not consider me unknown anymore!", my_port);
                    peer.connection_is_unknown = false;
                    continue;
                }
            }
    
            if msg.len() >= b"ENDPOINT EVIDENCE".len() && &msg[0..b"ENDPOINT EVIDENCE".len()] == b"ENDPOINT EVIDENCE" {
                let evidence = EndpointEvidence::read_from(&msg[b"ENDPOINT EVIDENCE".len()..]).unwrap();

                if let Some(i) = peers.iter().position(|p| p.root_public_key == evidence.root_public_key) {
                    peers[i].endpoint = Some(evidence.endpoint);
                    roster_endpoint_evidence.retain(|e| e.root_public_key != evidence.root_public_key);
                    roster_endpoint_evidence.push(evidence);
                }
                continue;
            } else {
                // println!("{}:  From known peer!   field={:016X} Got '{:?}' from {}", my_port, peer.nonce_ack_field, msg, addr);
                continue;
            }
        }
    }
}

const PACKET_TYPE_HEARTBEAT : u8 = 0;

// Note(Sam): Heart beat should be different by connection type or contain information regarding the connection type.
struct PacketHeartbeat {
    nonce_ack_latest: u64,
    nonce_ack_field: u64,
}
impl PacketHeartbeat {
    pub fn write_to<W: Write>(&self, mut w: W) -> std::io::Result<()> {
        w.write_u64::<LittleEndian>(self.nonce_ack_latest)?;
        w.write_u64::<LittleEndian>(self.nonce_ack_field)?;
        Ok(())
    }

    pub fn read_from<R: Read>(mut r: R) -> std::io::Result<Self> {
        let nonce_ack_latest = r.read_u64::<LittleEndian>()?;
        let nonce_ack_field = r.read_u64::<LittleEndian>()?;
        Ok(Self {
            nonce_ack_latest,
            nonce_ack_field,
        })
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

#[cfg(test)]
mod tests {
    use std::net::Ipv4Addr;

    use super::*;

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

        let static_private_keys : Vec<_> = (0..4).map(|_| {
            let mut crypto_rng = ChaCha20Rng::seed_from_u64(rand::rng().next_u64());
            // NOTE: doing this manually to avoid CryptoRng incompatibilities between different rand_core versions
            let mut secret_key = [0u8; 32];
            crypto_rng.fill_bytes(&mut secret_key);
            ed25519_zebra::SigningKey::from(secret_key)
        }).collect();
        let roster : Vec<VerificationKeyBytes> = static_private_keys.iter().map(|sk| sk.verification_key().into()).collect();
        let roster : Vec<[u8; 32]> = roster.into_iter().map(|p|p.into()).collect();

        let static_keypair_zero = {
            let kp = snow::Builder::new("Noise_IK_25519_ChaChaPoly_BLAKE2s".parse().unwrap()).generate_keypair().unwrap();
            StaticDHKeyPair { private: kp.private.try_into().unwrap(), public: kp.public.try_into().unwrap(), }
        };

        let endpoint_zero : SecureUdpEndpoint = {
            let ip = "127.0.0.1".parse::<Ipv4Addr>().unwrap().to_ipv6_mapped();
            let port : u16 = 3030;
            SecureUdpEndpoint { ip_address: ip.octets(), port, public_key: static_keypair_zero.public }
        };

        let evidence_zero = {
            EndpointEvidence { endpoint: endpoint_zero, root_public_key: static_private_keys[0].verification_key().into() }
        };

        let _joins = [
            rt.spawn(instance(static_private_keys[0], Some(static_keypair_zero), Some(endpoint_zero), roster.clone(), vec![evidence_zero], None)),
            rt.spawn(instance(static_private_keys[1], None, None, roster.clone(), vec![evidence_zero], None)),
            rt.spawn(instance(static_private_keys[2], None, None, roster.clone(), vec![evidence_zero], None)),
            rt.spawn(instance(static_private_keys[3], None, None, roster.clone(), vec![evidence_zero], None)),
        ];

        rt.block_on(std::future::pending::<()>())
    }
}
