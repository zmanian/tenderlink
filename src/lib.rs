#![allow(dead_code)]
#![allow(unused_parens)]
#![allow(clippy::never_loop)]

#![allow(clippy::eq_op)]
const PRINT_ROSTER:         bool = 0 == 1;
const PRINT_NETWORK_STATS:  bool = 1 == 1;
const PRINT_PEERS:          bool = 0 == 1;
const PRINT_VALID_INCOMING: bool = 0 == 1;
const PRINT_SENDS:          bool = 0 == 1;
const PRINT_SEND_CS:        bool = 0 == 1;
const PRINT_RNGS:           bool = 0 == 1;
const PRINT_BFT_PROPOSAL:   bool = 1 == 1;
const PRINT_BFT_VOTE:       bool = 1 == 1;
const PRINT_BFT_UPDATE:     bool = 1 == 1;
const PRINT_BFT_STATE:      bool = 0 == 1;
const PRINT_BFT_CONDITIONS: bool = 1 == 1;
const PRINT_BFT_TIMEOUTS:   bool = 1 == 1;


// MTU discovery is an option, but for now we're adopting a very conservative and VPN-friendly fixed-value MTU.
const ETHERNET_FRAME_SIZE:   usize = 1500;
const IPV6_HEADER_SIZE:      usize =   40;
const UDP_HEADER_SIZE:       usize =    8;
const PPPOE_HEADER_SIZE:     usize =    8;
const WIREGUARD_HEADER_SIZE: usize =   40;
const VPN_HEADER_SIZE:       usize =   64; // relatively conservative(?) OpenVPN header overhead size
const NOISE_NONCE_SIZE:      usize =    8;
const NOISE_HEADER_SIZE:     usize =   16;

const MAX_PATH_HEADERS_SIZE: usize = (IPV6_HEADER_SIZE + UDP_HEADER_SIZE + WIREGUARD_HEADER_SIZE + VPN_HEADER_SIZE + NOISE_NONCE_SIZE + NOISE_HEADER_SIZE);

const PATH_MTU: usize = ETHERNET_FRAME_SIZE - MAX_PATH_HEADERS_SIZE;

use static_assertions::{const_assert};
use std::{io::{Cursor, Read}, net::{Ipv6Addr, SocketAddr, SocketAddrV6}, sync::{Arc, Mutex}};
use byteorder::{LittleEndian, ReadBytesExt};
use ed25519_zebra::{Signature, SigningKey, VerificationKeyBytes, VerificationKey};
use rand::{seq::{IndexedRandom}, Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use rand_pcg::Lcg128CmDxsm64 as SimRng;
use snow::{resolvers::CryptoResolver, HandshakeState, StatelessTransportState};
use tokio::time::Instant;

const TICK_DURATION: std::time::Duration = std::time::Duration::from_millis(300);
const TIMEOUT_DURATION: std::time::Duration = std::time::Duration::from_millis(10000);
const NONCE_FORWARD_JUMP_TOLERANCE: u64 = 512;

fn is_timeout(e: std::io::ErrorKind) -> bool{
    e == std::io::ErrorKind::WouldBlock || e == std::io::ErrorKind::TimedOut
}

#[derive(Clone, Debug)]
pub struct SortedRosterMember {
    pub pub_key: PubKeyID,
    pub stake: u64,
    pub cumulative_stake: u64, // everyone in array prior to this point (used for determining proposer)
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum TMStep {
    Propose,
    Prevote,
    // ALT: extra sign step
    Precommit,
}

#[derive(Debug)]
struct TMDecision {
    round_i: usize,
    value: BlockValue,
    //signatures: Vec<TMSig>, // ability to prove to others e.g. those catching up
}


struct TMVote {
    approve: bool,
    todo_sign_bytes: [u8; 96],
}

#[derive(Clone, PartialEq, Debug)]
pub struct BlockValue(pub Vec<u8>); // NOTE (azmr): currently exactly-divided by chunk size for simplicity
impl BlockValue {
    fn id_from_value(&self, hash_keys: &HashKeys) -> ValueId { ValueId(hash_keys.value_id.hash(&self.0)) }
    fn chunks_n(&self) -> usize { self.0.len().div_ceil(PROPOSAL_CHUNK_DATA_SIZE) }
    fn chunk_o_size(&self, chunk_i: usize) -> (usize, usize) {
        let o = chunk_i * PROPOSAL_CHUNK_DATA_SIZE;
        (o, usize::min(PROPOSAL_CHUNK_DATA_SIZE, self.0.len() - o))
    }
}

#[derive(Clone)]
pub struct ClosureToProposeNewBlock(pub Arc<dyn Fn() -> core::pin::Pin<Box<dyn Future<Output = Option<BlockValue>> + Send>> + Send + Sync + 'static>);
impl std::fmt::Debug for ClosureToProposeNewBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ClosureToProposeNewBlock(..)")
    }
}
#[derive(Clone)]
pub struct ClosureToValidateProposedBlock(pub Arc<dyn for<'a> Fn(&'a BlockValue)-> core::pin::Pin<Box<dyn Future<Output = TMStatus> + Send + 'a>> + Send + Sync + 'static>);
impl std::fmt::Debug for ClosureToValidateProposedBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ClosureToValidateProposedBlock(..)")
    }
}
#[derive(Clone)]
pub struct ClosureToPushDecidedBlock(pub Arc<dyn Fn(BlockValue, FatPointerToBftBlock3)-> core::pin::Pin<Box<dyn Future<Output = Vec<SortedRosterMember>> + Send>> + Send + Sync + 'static>);
impl std::fmt::Debug for ClosureToPushDecidedBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ClosureToPushDecidedBlock(..)")
    }
}
#[derive(Clone)]
pub struct ClosureToGetHistoricalBlock(pub Arc<dyn Fn(u64)-> core::pin::Pin<Box<dyn Future<Output = (BlockValue, FatPointerToBftBlock3)> + Send>> + Send + Sync + 'static>);
impl std::fmt::Debug for ClosureToGetHistoricalBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ClosureToGetHistoricalBlock(..)")
    }
}

/// A bundle of signed votes for a block
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)] //, serde::Serialize, serde::Deserialize)]
pub struct FatPointerToBftBlock3 {
    pub vote_for_block_without_finalizer_public_key: [u8; 76 - 32],
    pub signatures: Vec<FatPointerSignature3>,
}

impl std::fmt::Display for FatPointerToBftBlock3 {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{{hash:")?;
        for b in &self.vote_for_block_without_finalizer_public_key[0..32] {
            write!(f, "{:02x}", b)?;
        }
        write!(f, " ovd:")?;
        for b in &self.vote_for_block_without_finalizer_public_key[32..] {
            write!(f, "{:02x}", b)?;
        }
        write!(f, " signatures:[")?;
        for (i, s) in self.signatures.iter().enumerate() {
            write!(f, "{{pk:")?;
            for b in s.public_key {
                write!(f, "{:02x}", b)?;
            }
            write!(f, " sig:")?;
            for b in s.vote_signature {
                write!(f, "{:02x}", b)?;
            }
            write!(f, "}}")?;
            if i + 1 < self.signatures.len() {
                write!(f, " ")?;
            }
        }
        write!(f, "]}}")?;
        Ok(())
    }
}

fn round_data_to_fat_pointer(round_data: &RoundData, roster: &[SortedRosterMember]) -> FatPointerToBftBlock3 {
    let vote_for_block_without_finalizer_public_key: [u8; 76 - 32];
    {
        let mut sign_data = [0; 76 - 32];
        round_data.proposal_id.0.write_to(&mut sign_data[0..32]);
        round_data.height.write_to(&mut sign_data[32..]);
        (round_data.round + 0x8000_0000).write_to(&mut sign_data[40..]);
        vote_for_block_without_finalizer_public_key = sign_data;
    }

    FatPointerToBftBlock3 {
        vote_for_block_without_finalizer_public_key,
        signatures: round_data.msg_val_sigs
            .iter()
            .map(|x| &x[1])
            .enumerate()
            .filter_map(|(roster_i, (value_id, commit_signature))| {
                if *value_id == round_data.proposal_id && *commit_signature != TMSig::NIL {
                    Some(FatPointerSignature3 {
                        public_key: roster[roster_i].pub_key.0,
                        vote_signature: commit_signature.0,
                    })
                } else { None }
            })
            .collect(),
    }
}

impl FatPointerToBftBlock3 {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        buf.extend_from_slice(&self.vote_for_block_without_finalizer_public_key);
        buf.extend_from_slice(&(self.signatures.len() as u16).to_le_bytes());
        for s in &self.signatures {
            buf.extend_from_slice(&s.to_bytes());
        }
        buf
    }
    #[allow(clippy::reversed_empty_ranges)]
    pub fn try_from_bytes(bytes: &Vec<u8>) -> Option<FatPointerToBftBlock3> {
        if bytes.len() < 76 - 32 + 2 {
            return None;
        }
        let vote_for_block_without_finalizer_public_key = bytes[0..76 - 32].try_into().unwrap();
        let len = u16::from_le_bytes(bytes[76 - 32..2].try_into().unwrap()) as usize;

        if 76 - 32 + 2 + len * (32 + 64) > bytes.len() {
            return None;
        }
        let rem = &bytes[76 - 32 + 2..];
        let signatures = rem
            .chunks_exact(32 + 64)
            .map(|chunk| FatPointerSignature3::from_bytes(chunk.try_into().unwrap()))
            .collect();

        Some(Self {
            vote_for_block_without_finalizer_public_key,
            signatures,
        })
    }
}

/// A vote signature for a block
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)] //, serde::Serialize, serde::Deserialize)]
pub struct FatPointerSignature3 {
    pub public_key: [u8; 32],
    pub vote_signature: [u8; 64],
}

impl FatPointerSignature3 {
    pub fn to_bytes(&self) -> [u8; 32 + 64] {
        let mut buf = [0_u8; 32 + 64];
        buf[0..32].copy_from_slice(&self.public_key);
        buf[32..32 + 64].copy_from_slice(&self.vote_signature);
        buf
    }
    pub fn from_bytes(bytes: &[u8; 32 + 64]) -> FatPointerSignature3 {
        Self {
            public_key: bytes[0..32].try_into().unwrap(),
            vote_signature: bytes[32..32 + 64].try_into().unwrap(),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum TMStatus {
    Indeterminate,
    Pass, // 2f+1 yes
    Fail, // f+1 no
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct ValueId([u8; 32]);
impl ValueId { const NIL: Self = Self([0; 32]); }
impl std::fmt::Display for ValueId { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { fmt_byte_str(f, &self.0) } }
impl std::fmt::Debug   for ValueId { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { fmt_prefixed_byte_str(f, "VId{", &self.0)?; write!(f, "}}") } }

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PubKeyID(pub [u8; 32]);
impl PubKeyID { const NIL: Self = Self([0; 32]); }
impl std::fmt::Display for PubKeyID { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { fmt_byte_str(f, &self.0) } }
impl std::fmt::Debug   for PubKeyID { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { fmt_prefixed_byte_str(f, "Pub{", &self.0[..2])?; write!(f, "}}") } }

#[derive(Clone, Copy, PartialEq, Eq)]
struct TMSig ([u8; 64]);
impl TMSig { const NIL: Self = Self([0; 64]); }
impl std::fmt::Debug for TMSig { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { fmt_prefixed_byte_str(f, "Sig{", &self.0[..2])?; write!(f, "}}") } }

#[derive(Debug, Clone)]
struct RoundData {
    height: u64,
    round: u32,
    // parallel with sorted roster arrays
    // TODO: keep parallel with each other, but be sparse in members
    proposal: BlockValue,
    proposal_valid_round: i64,
    proposal_sigs: Vec<TMSig>,
    proposal_sigs_n: usize, // filling sigs with random-access
    proposal_id: ValueId,
    proposal_checked_validity: TMStatus,
    // TODO: handle early outs because of this
    proposal_is_faulty: bool,

    // TODO: we may be able to compress valueid, but we do need to track it before we have the proposal
    msg_val_sigs: Vec<[(ValueId, TMSig); 2]>, // prevote then precommit
    roster: Vec<SortedRosterMember>,

    counts: ConsensusCounts,
    // TODO: can probably do this from whether *our* node has a valid value
    // TODO: by round or for whole state?
    active_timeout: Option<Timeout>,
    timeout_triggered: [bool; 2],
}
impl RoundData {
    const EMPTY: RoundData = RoundData {
        height: 0,
        round: 0,
        proposal: BlockValue(Vec::new()), // NOTE(azmr): don't alloc until we know the size (signed by proposer)
        proposal_valid_round: -1,
        proposal_sigs: Vec::new(),
        proposal_sigs_n: 0,
        proposal_id: ValueId::NIL,
        proposal_checked_validity: TMStatus::Indeterminate,
        proposal_is_faulty: false,
        // TODO: probably put both step messages next to each other
        msg_val_sigs: Vec::new(),
        roster: Vec::new(),
        counts: ConsensusCounts::ZERO,

        active_timeout: None,
        timeout_triggered: [false;2],
    };

    fn has_full_proposal(&self) -> bool {
        self.proposal_sigs_n > 0 && self.proposal_sigs_n == self.proposal_sigs.len()
    }
    fn has_enough_info_to_determine_validity(&self) -> bool {
        self.proposal_is_faulty || self.has_full_proposal()
    }
    // auto-caching
    async fn proposal_is_valid(&mut self, validate_closure: ClosureToValidateProposedBlock) -> TMStatus {
        // TODO: may want to start doing some of these on < proposal_chunks_n, i.e. shortcut known-invalid
        if self.proposal_checked_validity == TMStatus::Indeterminate {
            if self.proposal_is_faulty {
                self.proposal_checked_validity = TMStatus::Fail;
            } else if self.has_full_proposal() {
                self.proposal_checked_validity = validate_closure.0(&self.proposal).await;
            }
        }
        self.proposal_checked_validity
    }
}

enum TMMsgData {
    Proposal(BlockValue, i64),
    Prevote(ValueId),
    Precommit(ValueId),
}
struct TMMsg {
    height: u64,
    round: u32,
    data: TMMsgData, // ALT: byteslice + step distinguisher
    sig: TMSig,
}

#[derive(Clone, Copy, PartialEq)]
struct ConsensusCounts {
    anys: usize,
    prevotes: usize,
    nil_prevotes: usize,
    yes_prevotes: usize,
    precommits: usize,
    yes_precommits: usize,
}
impl ConsensusCounts {
    const ZERO: Self = Self {
        anys: 0,
        prevotes: 0,
        precommits: 0,
        yes_prevotes: 0,
        yes_precommits: 0,
        nil_prevotes: 0,
    };

    fn from_slice(slice: &[[(ValueId, TMSig); 2]]) -> Self {
        let mut counts = Self::ZERO;
        for el in slice {
            counts = counts + ConsensusCounts::from(el);
        }
        counts
    }
}
impl std::ops::Add for ConsensusCounts {
    type Output = Self;
    fn add(self, rhs: ConsensusCounts) -> ConsensusCounts {
        ConsensusCounts {
            anys:           self.anys           + rhs.anys,
            prevotes:       self.prevotes       + rhs.prevotes,
            nil_prevotes:   self.nil_prevotes   + rhs.nil_prevotes,
            yes_prevotes:   self.yes_prevotes   + rhs.yes_prevotes,
            precommits:     self.precommits     + rhs.precommits,
            yes_precommits: self.yes_precommits + rhs.yes_precommits,
        }
    }
}
impl std::ops::Sub for ConsensusCounts {
    type Output = Self;
    fn sub(self, rhs: ConsensusCounts) -> ConsensusCounts {
        ConsensusCounts {
            anys:           self.anys           - rhs.anys,
            prevotes:       self.prevotes       - rhs.prevotes,
            nil_prevotes:   self.nil_prevotes   - rhs.nil_prevotes,
            yes_prevotes:   self.yes_prevotes   - rhs.yes_prevotes,
            precommits:     self.precommits     - rhs.precommits,
            yes_precommits: self.yes_precommits - rhs.yes_precommits,
        }
    }
}
impl From<&[(ValueId, TMSig); 2]> for ConsensusCounts {
    fn from(val: &[(ValueId, TMSig); 2]) -> ConsensusCounts {
        let has_sigs     = [(val[0].1 != TMSig::NIL) as usize, (val[1].1 != TMSig::NIL) as usize];
        let has_any_sigs = has_sigs[0] | has_sigs[1]; // TODO: confirm prevote + precommit from the same person counts as 1

        let mut status = [[0,0], [0,0]];
        status[0][(val[0].0 != ValueId::NIL) as usize] = has_sigs[0];
        status[1][(val[1].0 != ValueId::NIL) as usize] = has_sigs[1];

        ConsensusCounts {
            anys: has_any_sigs,
            prevotes: has_sigs[0],
            nil_prevotes: status[0][0],
            yes_prevotes: status[0][1],
            precommits: has_sigs[1],
            yes_precommits: status[1][1],
        }
    }
}
impl std::fmt::Debug for ConsensusCounts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Counts {{ a:{}  v:{} (nv:{} yv:{})  c:{} (yc:{}) }}",
            self.anys,
            self.prevotes,
            self.nil_prevotes,
            self.yes_prevotes,
            self.precommits,
            self.yes_precommits,
        )
    }
}


fn roster_i_from_pub_key(roster: &[SortedRosterMember], pub_key: PubKeyID) -> Option<usize> {
    roster.iter().position(|m| m.pub_key == pub_key)
}

#[derive(Debug, Clone)]
struct Timeout { time: Instant, height: u64, round: u32, step: TMStep }
impl Timeout {
    fn new(now: Instant, height: u64, round: u32, step: TMStep) -> Timeout {
        use std::time::Duration;
        let timeout = match step {
            // Note(Sam): These timeout should be tuned to match the maximum network load block time. An additional
            // virtue of a short block time that I had not considered is that it hides round stalls better.
            TMStep::Propose   => Duration::from_millis(2000) + round * Duration::from_millis(500),
            TMStep::Prevote   => Duration::from_millis(2000) + round * Duration::from_millis(500),
            TMStep::Precommit => Duration::from_millis(2000) + round * Duration::from_millis(500),
        };

        Timeout{ time: now + timeout, height, round, step }
    }
}


const ROSTER_MAX_N: usize = 100;
fn active_roster_len(roster: &[SortedRosterMember]) -> usize { usize::min(ROSTER_MAX_N, roster.len()) }
fn total_roster_len(roster: &[SortedRosterMember])  -> usize { roster.len() }

#[derive(PartialEq, Debug, Clone, Copy)]
pub struct HashKey(pub [u8; 32]);
impl HashKey { const NIL: Self = Self([0;32]); }
impl HashKey {
    fn hasher(&self)            -> blake3::Hasher { blake3::Hasher::new_keyed(&self.0) }
    fn hash(&self, data: &[u8]) -> [u8; 32]       { *blake3::keyed_hash(&self.0, data).as_bytes() }
}

#[derive(Debug)]
pub struct HashKeys {
    pub proposer: HashKey,
    pub value_id: HashKey,
    pub connect_contention: HashKey,
    pub proposal_sig: HashKey,
}
impl Default for HashKeys {
    fn default() -> Self {
        Self {
            proposer:           HashKey(blake3::Hasher::new_derive_key("BFT Proposer")          .finalize().into()),
            value_id:           HashKey(blake3::Hasher::new_derive_key("BFT Value ID")          .finalize().into()),
            connect_contention: HashKey(blake3::Hasher::new_derive_key("BFT Connect Contention").finalize().into()), // NOTE(azmr): skipping update
            proposal_sig:       HashKey(blake3::Hasher::new_derive_key("BFT Proposal Signature").finalize().into()),
        }
    }
}

#[derive(Debug)]
struct TMState {
    hash_keys: HashKeys,
    my_port: u16,
    my_signing_key: SigningKey,
    my_pub_key: PubKeyID,
    round: u32,
    step: TMStep,
    /// basically the chain of agreed blocks
    height: u64,
    /// most recent "possible decision value" - successful proposal + prevote
    /// when valid_value was updated
    valid_value_round: (Option<BlockValue>, i64), // TODO
    /// last value sent for precommit // TODO: non-nil only?
    /// last round on which a *non-nil* value was sent
    locked_value_round: (Option<BlockValue>, i64), // TODO

    rounds_data: Vec<RoundData>,

    recent_commit_round_cache: Vec<RoundData>, // for now will hold all completed heights

    propose_closure: ClosureToProposeNewBlock,
    validate_closure: ClosureToValidateProposedBlock,
    push_block_closure: ClosureToPushDecidedBlock,
    get_block_closure: ClosureToGetHistoricalBlock,
}
impl TMState {
    fn init(my_signing_key: SigningKey, my_pub_key: PubKeyID, my_port: u16, propose_closure: ClosureToProposeNewBlock, validate_closure: ClosureToValidateProposedBlock, push_block_closure: ClosureToPushDecidedBlock, get_block_closure: ClosureToGetHistoricalBlock) -> Self {
        Self {
            hash_keys: HashKeys::default(),
            my_port,
            my_signing_key,
            my_pub_key,
            round: 0,
            step: TMStep::Propose,
            height: 0,
            valid_value_round: (None, -1), // TODO: is this actually protocol-relevant or just a cache?
            locked_value_round: (None, -1),

            rounds_data: Vec::new(),
            recent_commit_round_cache: Vec::new(),

            propose_closure,
            validate_closure,
            push_block_closure,
            get_block_closure,
        }
    }

    // NOTE: we just add our info to our round data & have it become equivalent to everyone else's...
    fn broadcast(&mut self, roster: &[SortedRosterMember], round_i: usize, msg: TMMsgData) -> TMStep {
        // TODO: can we get away with not signing the step or separately signing the step?
        let mut buf = [0u8; 2048];
        // TODO: send to self
        // TODO: send to (some) others
        let height   = self.rounds_data[round_i].height;
        let round    = self.rounds_data[round_i].round;
        let Some(roster_i) = roster_i_from_pub_key(roster, self.my_pub_key) else {
            eprintln!("{} \x1b[91mBFT ERROR\x1b[0m: failed to find my own public key in the roster", self.ctx_str(roster));
            return self.step;
        };
        match msg {
            TMMsgData::Proposal(proposal, valid_round) => {
                let mut hdr = PacketProposalChunkHeader {
                    height, round, chunk_i: 0,
                    proposal_size: proposal.0.len().try_into().unwrap(),
                    proposal_id: /*if proposal.0[1] % 5 == 0 { ValueId([6;32]) } else*/ { proposal.id_from_value(&self.hash_keys) },
                    valid_round,
                };

                for chunk_i in 0..proposal.chunks_n() { // NOTE: excluding packet_type // TODO: check this
                    hdr.chunk_i = chunk_i as u32;
                    let mut o = 0;
                    o += hdr.write_to(&mut buf[0..]);

                    let (chunk_o, chunk_size) = proposal.chunk_o_size(chunk_i);
                    o += proposal.0[chunk_o..chunk_o + chunk_size].write_to(&mut buf[o..]);

                    // NOTE: we *DON'T* want to write it immediately to our proper store because it
                    // will confuse check_and_incorporate_msg
                    let sig = self.my_signing_key.sign(&buf[..o]).to_bytes();

                    // NOTE: we're faulty if we give our pub key for this if it's not our proposal
                    self.check_and_incorporate_msg(
                        height, round, chunk_i, hdr.proposal_id, hdr.valid_round,
                        roster, roster_i, PACKET_TYPE_PROPOSAL_CHUNK, &buf[..o], &sig
                    );
                }

                TMStep::Propose
            }

            TMMsgData::Prevote(value_id) | TMMsgData::Precommit(value_id) => {
                let is_precommit: u8 = if let TMMsgData::Precommit(..) = msg { 1 } else { 0 };
                if PRINT_BFT_VOTE { println!("{} {} on {}", self.ctx_str(roster), ["prevoting", "precommitting"][is_precommit as usize], value_id); }
                let packet_type = PACKET_TYPE_PREVOTE_SIGNATURES + is_precommit;
                let signed_data = make_vote_sign_datas(roster[roster_i].pub_key.0, is_precommit != 0, height, round, value_id)[1];
                let sig         = self.my_signing_key.sign(&signed_data).to_bytes();

                self.check_and_incorporate_msg(
                    height, round, 0, value_id, -2,
                    roster, roster_i, packet_type, &signed_data, &sig
                );

                [TMStep::Prevote, TMStep::Precommit][is_precommit as usize]
            },
        }
    }

    /// Deterministic weighted round robin (hash & mod total zec on cumulative list)
    fn proposer_from_height_round(hash_keys: &HashKeys, roster: &[SortedRosterMember], height: u64, round: u32) -> (Option<usize>, PubKeyID) {
        if roster.len() == 0 {
            eprintln!("\x1b[91mBFT ERROR\x1b[0m: trying to get proposer from empty roster");
            return (None, PubKeyID::NIL); // TODO: is a fixed value here exploitable? Presumably nobody can sign for it?
        }

        // NOTE(azmr): this 32-byte crypto-hashing is almost certainly overkill!
        let hash = hash_keys.proposer.hasher().update(&u64::to_le_bytes(height)).update(&u32::to_le_bytes(round)).finalize();

        let mut hash_stake_bytes = [0; 8];
        hash.as_bytes()[..8].write_to(&mut hash_stake_bytes);
        let hash_stake = u64::from_le_bytes(hash_stake_bytes);

        let last_included_i = active_roster_len(roster) - 1;
        let total_included_stake = roster[last_included_i].cumulative_stake;
        if total_included_stake == 0 {
            eprintln!("\x1b[91mBFT ERROR\x1b[0m: all roster members have no stake");
            return (None, PubKeyID::NIL); // TODO: is a fixed value here exploitable? Presumably nobody can sign for it?
        }


        let proposer_stake = hash_stake % total_included_stake;

        let roster_i = roster.partition_point(|m| m.cumulative_stake <= proposer_stake);
        // println!("proposer stake hash: {} ==u64=> {:016x} ==%{}=> {} ==i=> {}", hash, hash_stake, total_included_stake, proposer_stake, roster_i);
        (Some(roster_i), roster[roster_i].pub_key)
    }

    fn insert_round(&mut self, insert_i: usize, round: u32, roster: &[SortedRosterMember]) -> usize {
        let roster_n = active_roster_len(roster);
        self.rounds_data.insert(insert_i, RoundData {
            height: self.height,
            round,
            msg_val_sigs: vec![[(ValueId::NIL, TMSig::NIL); 2]; roster_n], // TODO: just use ROSTER_MAX_N?
            roster: roster.to_vec(),
            ..RoundData::EMPTY
        });
        insert_i
    }

    async fn start_round(&mut self, roster: &[SortedRosterMember], now: Instant, round: u32) {
        self.round = round;
        // self.active_proposal_value_round = (None, -1);

        let round_i = match self.rounds_data.binary_search_by_key(&(self.height, round), |el| (el.height, el.round)) {
            Ok(round_i)  => round_i,
            Err(round_i) => self.insert_round(round_i, round, roster)
        };

        if Self::proposer_from_height_round(&self.hash_keys, roster, self.height, round).1 == self.my_pub_key {
            let proposal = if let Some(valid_value) = self.valid_value_round.0.clone() {
                Some(valid_value)
            } else {
                self.propose_closure.0().await
            };
            if PRINT_BFT_PROPOSAL { if let Some(proposal) = &proposal { println!("{} about to propose with status '{:?}': {:?}", self.ctx_str(roster), self.validate_closure.0(&proposal).await, proposal); } }

            // TODO: simple approach: send proposal messages to self when broadcasting
            // self.active_proposal_value_round = (Some(proposal), self.valid_value_round.1);
            if let Some(proposal) = proposal {
                self.step = self.broadcast(roster, round_i, TMMsgData::Proposal(proposal, self.valid_value_round.1));
            } else {
                self.step = TMStep::Propose;
            }
        } else {
            self.step = TMStep::Propose;
        }
        self.rounds_data[round_i].active_timeout = Some(Timeout::new(now, self.height, self.round, TMStep::Propose));
    }

    fn f_from_n(n: u64) -> u64 {
        (n - 1) / 3
    }

    fn check_and_incorporate_msg(&mut self, height: u64, round: u32, chunk_i: usize, value_id: ValueId, valid_round: i64, roster: &[SortedRosterMember], roster_i: usize, packet_type: u8, signed_data: &[u8], sig_data: &[u8;64]) -> TMStatus {
        let me_str  = self.ctx_str(roster);
        let pkt_str = format!("{:20} {}.{}.{}", packet_name_from_type(packet_type), height, round, chunk_i);

        if height != self.height {
            // eprintln!("{}: BFT: received [{}] when we're at height {}", me_str, pkt_str, self.height);
            return TMStatus::Fail;
        }

        // check if in (active) roster
        if roster_i >= active_roster_len(roster) {
            eprintln!("{} [{}]: \x1b[91mBFT FAULT\x1b[0m: {} is not in the active roster.", me_str, pkt_str, roster_i);
            return TMStatus::Fail;
        }

        let from_pub_key = roster[roster_i].pub_key;

        // pkt_str += &format!(" from {} ({})", roster_i, from_pub_key);
        let ctx_str = format!("{} [{} from {} {:?}]", me_str, pkt_str, roster_i, from_pub_key);

        // check if data was signed by pub key
        let signature = Signature::from_bytes(sig_data);
        let vk = match VerificationKey::try_from(from_pub_key.0) { Ok(v)=>v, Err(err)=>{
            eprintln!("{}: \x1b[91mBFT FAULT\x1b[0m: invalid public key: {} ({})", ctx_str, from_pub_key, err);
            return TMStatus::Fail;
        }};
        match vk.verify(&signature, signed_data) { Ok(_)=>{}, Err(err)=>{
            eprintln!("{}: \x1b[91mBFT FAULT\x1b[0m: invalid signature[..{}]: {} {}", ctx_str, signed_data.len(), value_id, err);
            return TMStatus::Fail;
        }}
        let sig = TMSig(*sig_data);

        if PRINT_VALID_INCOMING { eprintln!("{}: valid signature for value id: {}", ctx_str, value_id); }

        // TODO: other checks
        // - data size check if we're doing network stuff

        let (is_prev_seen_round, round_i) = match self.rounds_data.binary_search_by_key(&(height, round), |el| (el.height, el.round)) {
            Ok(round_i)  => (true,  round_i),
            Err(round_i) => (false, self.insert_round(round_i, round, roster)),
        };
        let round_data = &mut self.rounds_data[round_i];

        // TODO: Keep a dynamic array to solve the "Amnesiac Proposer's Dilemma".
        //       If I propose my block for this height and round, but then my
        //       computer gets unplugged, I've forgotten block history and need to
        //       catch back up to the network's consensus height. However, on the
        //       way there, I'll sometimes propose new values. (This is expected,
        //       arguably, since we never truly know whether we're at the top of
        //       the consensus height.) However, in the process of catching up I
        //       may get my own *different* signed proposal that was already decided!
        //       Normally we would mark that proposer as faulty/adversarial, but we
        //       assume that we are never faulty, and must therefore be "amnesic".
        //       In Byzantine scenarios I may have been unplugged arbitrarily
        //       many times and be receiving arbitrarily many validly signed
        //       proposals of my own making, with even some signed precommits.
        //       We'll observe multiple competing proposals, all signed by us, all
        //       equally valid candidates for the decisive proposal, any of which
        //       may establish consensus. We won't know until we see 2f+1 precommits.
        //       We need to let these precommits *race*, until we observe 2f+1
        //       stake being precommitted to *any* of our proposals, at which
        //       point we accept *that* proposal as decisive. (There will never
        //       be multiple proposals with 2f+1 precommits unless the BFT
        //       network is faulty; we just need to wait and see which one
        //       is the decisive one.)  -Phil 2025-10-20
        // NOTE: @Incomplete: for now, only track the latest proposal.
        let is_my_proposal = (from_pub_key == self.my_pub_key);

        match packet_type {
            PACKET_TYPE_PROPOSAL_CHUNK => {
                let Ok(hdr) = PacketProposalChunkHeader::read_from(signed_data) else {
                    return TMStatus::Fail
                };

                // "have they previously proposed a different value?"
                if is_prev_seen_round && round_data.proposal_sigs_n > 0 {
                    if is_my_proposal &&
                      (round_data.proposal.0.len() != hdr.proposal_size as usize ||
                       round_data.proposal_id != value_id ||
                       round_data.proposal_valid_round != valid_round) { // Amnesiac Proposer's Dilemma
                        // Flush proposal id/votes. @Robustness @Duplicate: how to tersely flush the round?
                        let roster_n = active_roster_len(roster);
                        *round_data = RoundData {
                            height:               round_data.height,
                            round:                round_data.round,
                            proposal_id:          value_id,
                            proposal_valid_round: valid_round,
                            msg_val_sigs:         vec![[(ValueId::NIL, TMSig::NIL); 2]; roster_n], // TODO: just use ROSTER_MAX_N?
                            roster:               Vec::from(&roster[0..roster_n]),
                            active_timeout:       round_data.active_timeout.clone(),
                            timeout_triggered:    round_data.timeout_triggered,
                            ..RoundData::EMPTY
                        };
                        round_data.proposal.0    = vec![0;          hdr.proposal_size as usize];
                        round_data.proposal_sigs = vec![TMSig::NIL; round_data.proposal.chunks_n()];
                        eprintln!("{}: \x1b[93mAMNESIAC PROPOSER\x1b[0m at {}.{}.{}: Flushing proposal...", ctx_str, height, round, chunk_i);
                    } else {
                        if round_data.proposal.0.len() != hdr.proposal_size as usize {
                            eprintln!("{}: \x1b[91mBFT FAULT\x1b[0m at {}.{}.{}: proposer {} proposed 2 different-size values ({:?}, {:?}). Ignoring latest...",
                            ctx_str, height, round, chunk_i, roster_i, round_data.proposal.0.len(), hdr.proposal_size);
                            return TMStatus::Fail;
                        }
                        if round_data.proposal_id != value_id {
                            // TODO: immediately class both as invalid?
                            eprintln!("{}: \x1b[91mBFT FAULT\x1b[0m at {}.{}.{}: proposer {} proposed 2 different values ({:?}, {:?}). Ignoring latest...",
                            ctx_str, height, round, chunk_i, roster_i, round_data.proposal_id, value_id);
                            return TMStatus::Fail;
                        }
                        if round_data.proposal_valid_round != valid_round {
                            // TODO: immediately class both as invalid
                            eprintln!("{}: \x1b[91mBFT FAULT\x1b[0m at {}.{}.{}: proposer {} proposed 2 different valid rounds ({}, {}). Ignoring latest...",
                            ctx_str, height, round, chunk_i, roster_i, round_data.proposal_valid_round, valid_round);
                            return TMStatus::Fail;
                        }
                    }
                } else {
                    round_data.proposal.0    = vec![0;          hdr.proposal_size as usize];
                    round_data.proposal_sigs = vec![TMSig::NIL; round_data.proposal.chunks_n()];
                }

                // Preliminary checks now finished (although not infallible from here) //////////////////////////

                // TODO: check expected proposer here if not above
                let (chunk_o, chunk_size) = round_data.proposal.chunk_o_size(chunk_i);
                let packet_chunk_o        = PacketProposalChunkHeader::SERIALIZED_SIZE;
                let chunk_data            = &signed_data[packet_chunk_o..packet_chunk_o + chunk_size];

                if round_data.proposal_sigs[chunk_i] == TMSig::NIL { // value chunk not seen before
                    chunk_data.write_to(&mut round_data.proposal.0[chunk_o..chunk_o+chunk_size]);
                    round_data.proposal_sigs[chunk_i] = sig;
                    round_data.proposal_sigs_n       += 1;
                    round_data.proposal_valid_round   = valid_round;
                    if round_data.proposal_id == ValueId::NIL { // first time we've seen any proposal chunks
                        round_data.proposal_id = value_id;

                        let mut prev_sig_had_fault = false;
                        // check whether speculative adds to round data were for the actual proposal
                        for roster_i in 0..round_data.msg_val_sigs.len() {
                            let msg_val: &mut [(ValueId, TMSig); 2] = &mut round_data.msg_val_sigs[roster_i];
                            for is_precommit in 0..2 {
                                if msg_val[is_precommit].0 != ValueId::NIL && msg_val[is_precommit].0 != value_id {
                                    prev_sig_had_fault = true;
                                    eprintln!("{}: \x1b[91mBFT FAULT\x1b[0m at {}.{}: finalizer {} {} on non-proposed value {}. Ignoring...", ctx_str, height, round, roster_i, ["prevoted","precommitted"][is_precommit], value_id);
                                    msg_val[is_precommit] = (ValueId::NIL, TMSig::NIL);
                                }
                            }
                        }

                        if prev_sig_had_fault { // recompute from scratch
                            // NOTE: this does NOT imply the current packet/proposal is faulty, so we should continue with it
                            round_data.counts = ConsensusCounts::from_slice(&round_data.msg_val_sigs);
                        }
                    }

                    if round_data.proposal_sigs_n == round_data.proposal_sigs.len() {
                        let check_value_id = round_data.proposal.id_from_value(&self.hash_keys);
                        if round_data.proposal_id != check_value_id {
                            round_data.proposal_is_faulty = true;
                            eprintln!("{}: \x1b[91mBFT FAULT\x1b[0m: proposer's value_id does not match our calculation: {} != {}",
                                ctx_str, round_data.proposal_id, check_value_id);
                            return TMStatus::Fail;
                        }
                    }

                    if PRINT_BFT_UPDATE { println!("{}: update to {}/{} proposal chunks on {}", ctx_str, round_data.proposal_sigs_n, round_data.proposal_sigs.len(), round_data.proposal_id); }

                    // TODO: include signed prevote & precommit for self?
                } else if round_data.proposal_sigs[chunk_i] != sig { // TODO: check value/sig conformance
                    if is_my_proposal { // Amnesiac Proposer's Dilemma
                        // Flush proposal id/votes. @Robustness @Duplicate: how to tersely flush the round?
                        let roster_n = active_roster_len(roster);
                        *round_data = RoundData {
                            height:               round_data.height,
                            round:                round_data.round,
                            proposal_id:          value_id,
                            proposal_valid_round: valid_round,
                            msg_val_sigs:         vec![[(ValueId::NIL, TMSig::NIL); 2]; roster_n], // TODO: just use ROSTER_MAX_N?
                            roster:               Vec::from(&roster[0..roster_n]),
                            active_timeout:       round_data.active_timeout.clone(),
                            timeout_triggered:    round_data.timeout_triggered,
                            ..RoundData::EMPTY
                        };
                        round_data.proposal.0    = vec![0;          hdr.proposal_size as usize];
                        round_data.proposal_sigs = vec![TMSig::NIL; round_data.proposal.chunks_n()];
                        eprintln!("{}: \x1b[93mAMNESIAC PROPOSER\x1b[0m at {}.{}.{}: Flushing proposal...", ctx_str, height, round, chunk_i);
                    } else {
                        // TODO: treat this as a failed is_valid & early out before awaiting full proposal
                        round_data.proposal_is_faulty = true;
                        eprintln!("{}: \x1b[91mBFT FAULT\x1b[0m: proposer signed 2 different values. Ignoring latest...", ctx_str);
                        return TMStatus::Fail;
                    }
                } else {
                    return TMStatus::Pass; // already good
                }

                TMStatus::Pass
            }


            PACKET_TYPE_PREVOTE_SIGNATURES | PACKET_TYPE_PRECOMMIT_SIGNATURES => {
                // TODO: check if this person has previously voted differently; is this covered later?
                let is_precommit = (packet_type - PACKET_TYPE_PREVOTE_SIGNATURES) as usize;

                let status = if value_id == ValueId::NIL { // always legal (except for duplicate checked later)
                    TMStatus::Pass
                } else if round_data.proposal_sigs_n == 0 {
                    // if we don't have a real proposal yet we can't check for validity
                    TMStatus::Indeterminate
                } else if round_data.proposal_id != value_id {
                    eprintln!("{}: \x1b[91mBFT FAULT\x1b[0m at {}.{}: finalizer {} voted on non-proposed value {}. Ignoring...", ctx_str, height, round, roster_i, value_id);
                    return TMStatus::Fail;
                } else {
                    TMStatus::Pass
                };

                // TODO: check if specified valid_round had a different value_id

                let old_val_sig = round_data.msg_val_sigs[roster_i][is_precommit];
                let new_val_sig = (value_id, sig);
                if old_val_sig.1 != TMSig::NIL && new_val_sig != old_val_sig {
                    // TODO: do we want to allow for NIL updating to valid?
                    eprintln!("{}: \x1b[91mBFT FAULT\x1b[0m at {}.{}: finalizer {} voted on 2 different values ({:?}, {:?}). Ignoring latest...", ctx_str, height, round, roster_i, new_val_sig, old_val_sig);
                    return TMStatus::Fail;
                }
                // Checks now finished //////////////////////////

                // Add the signature to the list & update counts
                let old_cs = ConsensusCounts::from(&round_data.msg_val_sigs[roster_i]);
                round_data.msg_val_sigs[roster_i][is_precommit] = new_val_sig;
                let new_cs = ConsensusCounts::from(&round_data.msg_val_sigs[roster_i]);
                let d = new_cs - old_cs; // add 1 to counts that have been updated by this message
                round_data.counts = round_data.counts + d;

                if PRINT_BFT_UPDATE && (
                    d.anys           |
                    d.prevotes       |
                    d.precommits     |
                    d.yes_prevotes   |
                    d.yes_precommits |
                    d.nil_prevotes) != 0 {
                    println!("{}: update to {:?} (d: {:?})", ctx_str, round_data.counts, d);
                }

                if true {
                    let check_counts = ConsensusCounts::from_slice(&round_data.msg_val_sigs);
                    if check_counts != round_data.counts {
                        eprintln!("{}: \x1b[91mBFT ERROR\x1b[0m: counts don't match: incremental: {:?}, absolute: {:?}", ctx_str, round_data.counts, check_counts);
                    }
                }

                status
            }


            _ => {
                eprintln!("{}: \x1b[91mBFT ERROR\x1b[0m: unexpected case: {}", ctx_str, packet_type);
                TMStatus::Fail
            }
        }
    }

    fn prune_unnecessary_data(&mut self) {
        // TODO (perf): drop 2f+1 nil-voted rounds before n-2
        todo!();
    }

    fn ctx_str(&self, roster: &[SortedRosterMember]) -> String {
        // format!("{:?} {:05}-{:?}-{:?}.{:3}.{:3}.{:9}", roster.into_iter().map(|m| m.pub_key).collect::<Vec<_>>(), self.my_port, self.my_pub_key, roster_i_from_pub_key(roster, self.my_pub_key), self.height, self.round, format!("{:?}", self.step))
        format!("{:05}-{:?}-{:?}.{:3}.{:3}.{:9}", self.my_port, self.my_pub_key, roster_i_from_pub_key(roster, self.my_pub_key), self.height, self.round, format!("{:?}", self.step))
    }
    fn name_str_other(roster: &[SortedRosterMember], peer: &Peer) -> String {
        format!("{:05}-{:?}-{:?}", peer.endpoint.unwrap_or_default().port, PubKeyID(peer.root_public_key), roster_i_from_pub_key(roster, PubKeyID(peer.root_public_key)))
    }

    async fn bft_update(&mut self, roster: &mut Vec<SortedRosterMember>) {
        let now = Instant::now();
        let f = Self::f_from_n(active_roster_len(roster) as u64) as usize;
        let ctx_str = self.ctx_str(roster);

        // NOTE: binary search to {current height, round 0} to avoid looping through data for unneeded decided heights
        let current_height_start_i = self.rounds_data.binary_search_by_key(&(self.height, 0), |el| (el.height, el.round)).unwrap_or(0);

        for i in current_height_start_i..self.rounds_data.len() {
            let counts = self.rounds_data[i].counts.clone();
            let has_enough_info_to_determine_validity = self.rounds_data[i].has_enough_info_to_determine_validity();

            // TODO: don't spam "while" messages repeatedly
            let is_current_height_and_round = (self.height, self.round) == (self.rounds_data[i].height, self.rounds_data[i].round);
            // println!("{:#?}", self);
            if PRINT_BFT_STATE {
                println!("{} {}={}.{}, {}/{}, {}", ctx_str,
                    ["!","="][is_current_height_and_round as usize],
                    self.rounds_data[i].height, self.rounds_data[i].round,
                    self.rounds_data[i].proposal_sigs_n, self.rounds_data[i].proposal_sigs.len(),
                    self.rounds_data[i].proposal_valid_round
                );
             }

            // line 11: init proposal period
            // (done elsewhere)

            // line 22: receive first proposal this height: prevote
            // > upon <PROPOSAL, h_p, round_p, v, −1> from proposer(h_p, round_p)
            // > while step_p = propose do
            // TODO: merge conditionals with below, they massively overlap
            if (is_current_height_and_round &&
                has_enough_info_to_determine_validity && // we have received the proposal value
                self.rounds_data[i].proposal_valid_round == -1 &&
                self.step == TMStep::Propose)
            {
                // TODO: do we want to prevote NIL on currently-indeterminate?
                // ALT: send NIL then later override with time-tagged message
                if self.rounds_data[i].proposal_is_valid(self.validate_closure.clone()).await == TMStatus::Pass && (
                    self.locked_value_round.1 == -1 ||
                    self.locked_value_round.0 == Some(self.rounds_data[i].proposal.clone())) // TODO(perf): use (previously-checked) ids for easier comparison?
                {
                    if PRINT_BFT_CONDITIONS { println!("{}: in condition 22-0: receive first proposal this height", ctx_str); }
                    self.step = self.broadcast(roster, i, TMMsgData::Prevote(self.rounds_data[i].proposal_id));
                } else {
                    if PRINT_BFT_CONDITIONS { println!("{}: in condition 22-1: receive first proposal this height", ctx_str); }
                    self.step = self.broadcast(roster, i, TMMsgData::Prevote(ValueId::NIL));
                }
            }

            // line 28: received 2f+1 prevotes: prevote
            // > upon <PROPOSAL, h_p, round_p, v, vr> from proposer(h_p, round_p) AND 2f+1 <PREVOTE, h_p, vr, id(v)>
            // > while step_p = propose && (0 <= vr && vr < round_p)
            if (is_current_height_and_round &&
                has_enough_info_to_determine_validity &&
                2*f+1 <= counts.yes_prevotes &&
                self.step == TMStep::Propose &&
                0 <= self.rounds_data[i].proposal_valid_round && self.rounds_data[i].proposal_valid_round < self.round as i64) // we have received the proposal value
            {
                if self.rounds_data[i].proposal_is_valid(self.validate_closure.clone()).await == TMStatus::Pass && (
                    self.locked_value_round.1 <= self.rounds_data[i].proposal_valid_round ||
                    self.locked_value_round.0 == Some(self.rounds_data[i].proposal.clone()))
                {
                    if PRINT_BFT_CONDITIONS { println!("{}: in condition 28-0: received 2f+1 prevotes", ctx_str); }
                    self.step = self.broadcast(roster, i, TMMsgData::Prevote(self.rounds_data[i].proposal_id));
                } else {
                    if PRINT_BFT_CONDITIONS { println!("{}: in condition 28-1: received 2f+1 prevotes", ctx_str); }
                    self.step = self.broadcast(roster, i, TMMsgData::Prevote(ValueId::NIL));
                }
            }

            // line 34: last orders on prevote period
            // > upon 2f+1 <PREVOTE, h_p, round_p, ∗> while step_p = prevote for the first time do
            if (is_current_height_and_round &&
                // don't need the proposal itself
                2*f+1 <= counts.prevotes &&
                self.step == TMStep::Prevote &&
                !self.rounds_data[i].timeout_triggered[0]) // "for the first time" // ALT: round.timeout_step != TMStep::Prevote
            {
                if PRINT_BFT_CONDITIONS { println!("{}: in condition 34: last orders on prevote period", ctx_str); }
                self.rounds_data[i].timeout_triggered[0] = true;
                self.rounds_data[i].active_timeout = Some(Timeout::new(now, self.height, self.round, TMStep::Prevote));
            }

            // line 36: seen 2f+1 valid prevotes: lock, valid, precommit
            // > upon <PROPOSAL, h_p, round_p, v, ∗> from proposer(h_p, round_p) AND 2f+1 <PREVOTE, h_p, round_p, id(v)>
            // > while valid(v) && step_p >= prevote for the first time do
            if (is_current_height_and_round &&
                has_enough_info_to_determine_validity &&
                2*f+1 <= counts.yes_prevotes &&
                self.rounds_data[i].proposal_is_valid(self.validate_closure.clone()).await == TMStatus::Pass &&
                (self.step == TMStep::Prevote || self.step == TMStep::Precommit)) // TODO: "for the first time"
            {
                if PRINT_BFT_CONDITIONS { println!("{}: in condition 36: seen 2f+1 valid prevotes", ctx_str); }
                if self.step == TMStep::Prevote {
                    if PRINT_BFT_CONDITIONS { println!("{}: in condition 36-0: seen 2f+1 valid prevotes", ctx_str); }
                    self.locked_value_round = (Some(self.rounds_data[i].proposal.clone()), self.round as i64);
                    self.step = self.broadcast(roster, i, TMMsgData::Precommit(self.rounds_data[i].proposal_id));
                }
                self.valid_value_round = (Some(self.rounds_data[i].proposal.clone()), self.round as i64);
            }

            // line 44: seen 2f+1 nil prevotes: precommit nil
            // > upon 2f+1 <PREVOTE, h_p, round_p, nil>
            // > while step_p = prevote do
            if (is_current_height_and_round &&
                2*f+1 <= counts.nil_prevotes &&
                self.step == TMStep::Prevote)
            {
                if PRINT_BFT_CONDITIONS { println!("{}: in condition 44: seen 2f+1 nil prevotes", ctx_str); }
                self.step = self.broadcast(roster, i, TMMsgData::Precommit(ValueId::NIL));
            }

            // line 47: last orders on precommit period
            // > upon 2f+1 <PRECOMMIT, h_p, round_p, ∗> for the first time do
            if (is_current_height_and_round &&
                2*f+1 <= counts.precommits &&
                !self.rounds_data[i].timeout_triggered[1])
            {
                if PRINT_BFT_CONDITIONS { println!("{}: in condition 47: last orders on precommit period", ctx_str); }
                self.rounds_data[i].timeout_triggered[1] = true;
                self.rounds_data[i].active_timeout = Some(Timeout::new(now, self.height, self.round, TMStep::Precommit));
            }

            // line 49: value decided
            // > upon <PROPOSAL, h_p, r, v, ∗> from proposer(h_p, r) AND 2f+1 <PRECOMMIT, h_p, r, id(v)>
            // > while decision_p[h_p] = nil do
            if (self.height == self.rounds_data[i].height && // any round
                has_enough_info_to_determine_validity &&
                2*f+1 <= counts.yes_precommits &&
                self.rounds_data[i].proposal_is_valid(self.validate_closure.clone()).await == TMStatus::Pass)
            {
                if PRINT_BFT_CONDITIONS { println!("{}: in condition 49: value decided", ctx_str); }
                let new_roster = self.push_block_closure.0(self.rounds_data[i].proposal.clone(), round_data_to_fat_pointer(&self.rounds_data[i], roster)).await;
                if PRINT_ROSTER { println!("{} new roster: {:?}", ctx_str, new_roster); }
                *roster = new_roster;
                self.height += 1;
                self.recent_commit_round_cache.push(self.rounds_data[i].clone());
                self.rounds_data.retain(|r| r.height < self.height);
                self.locked_value_round = (None, -1);
                self.valid_value_round = (None, -1);
                self.start_round(roster, now, 0).await;
            }

            // line 55: round catchup
            // > upon f+1 <∗, h_p, round, ∗, ∗> with round > round_p do
            if (self.height == self.rounds_data[i].height &&
                self.round    <  self.rounds_data[i].round  &&
                f+1 <= counts.anys)
            {
                if PRINT_BFT_CONDITIONS { println!("{}: in condition 55: round catchup", ctx_str); }
                self.start_round(roster, now, self.rounds_data[i].round).await
            }

            // timeouts
            if let Some(timeout) = &self.rounds_data[i].active_timeout &&
                timeout.time <= now &&
                self.height == timeout.height &&
                self.round    == timeout.round
            {
                // TODO(code): can we just use *our* step or is there a possible sequence issue? (from the presence of step checks, probably not)
                match timeout.step {
                    TMStep::Propose => if self.step == TMStep::Propose {
                        if PRINT_BFT_TIMEOUTS { println!("{}: hit timeout propose", ctx_str); }
                        self.step = self.broadcast(roster, i, TMMsgData::Prevote(ValueId::NIL));
                    },
                    TMStep::Prevote => if self.step == TMStep::Prevote {
                        if PRINT_BFT_TIMEOUTS { println!("{}: hit timeout prevote", ctx_str); }
                        self.step = self.broadcast(roster, i, TMMsgData::Precommit(ValueId::NIL));
                    },
                    TMStep::Precommit => {
                        if PRINT_BFT_TIMEOUTS { println!("{}: hit timeout precommit", ctx_str); }
                        self.start_round(roster, now, self.round + 1).await
                    },
                }
            }
        }
    }
}

// TODO: can we megastruct these and collapse the codepaths?
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

    unacted_upon_status_height: Option<u64>,
    latest_status: Option<PacketStatus>,
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
            unacted_upon_status_height: None,
            latest_status: None,
        }
    }
}

// NOTE: buf can be open-ended
trait SliceWrite         { fn write_to(&self, buf: &mut [u8]) -> usize; }
impl SliceWrite for u64  { fn write_to(&self, buf: &mut [u8]) -> usize { buf[0..8].copy_from_slice(&u64::to_le_bytes(*self)); 8 } }
impl SliceWrite for i64  { fn write_to(&self, buf: &mut [u8]) -> usize { buf[0..8].copy_from_slice(&i64::to_le_bytes(*self)); 8 } }
impl SliceWrite for u32  { fn write_to(&self, buf: &mut [u8]) -> usize { buf[0..4].copy_from_slice(&u32::to_le_bytes(*self)); 4 } }
impl SliceWrite for u16  { fn write_to(&self, buf: &mut [u8]) -> usize { buf[0..2].copy_from_slice(&u16::to_le_bytes(*self)); 2 } }
impl SliceWrite for u8   { fn write_to(&self, buf: &mut [u8]) -> usize { buf[0] = *self;                                      1 } }
impl SliceWrite for [u8] { fn write_to(&self, buf: &mut [u8]) -> usize { buf[0..self.len()].copy_from_slice(self);   self.len() } }


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
pub struct StaticDHKeyPair {
    private: [u8; 32],
    public: [u8; 32],
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct SecureUdpEndpoint {
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
    fn write_to(&self, buf: &mut [u8]) -> usize {
        self.public_key.write_to(&mut buf[..]);
        self.ip_address.write_to(&mut buf[32..]);
        self.port      .write_to(&mut buf[32+16..]);
        32+16+2
    }

    pub fn read_from<R: Read>(mut r: R) -> std::io::Result<Self> {
        let mut endpoint = SecureUdpEndpoint::default();
        r.read_exact(&mut endpoint.public_key)?;
        r.read_exact(&mut endpoint.ip_address)?;
        endpoint.port = r.read_u16::<LittleEndian>()?;
        Ok(endpoint)
    }
}

#[derive(Clone, Copy)]
pub struct EndpointEvidence {
    endpoint: SecureUdpEndpoint,
    root_public_key: [u8; 32],
}
impl Default for EndpointEvidence {
    fn default() -> EndpointEvidence {
        EndpointEvidence { endpoint: SecureUdpEndpoint::default(), root_public_key: [0_u8; 32] }
    }
}
impl EndpointEvidence {
    pub fn write_to(&self, buf: &mut [u8]) -> usize {
        let mut o = 0;
        o += self.endpoint       .write_to(&mut buf[o..]);
        o += self.root_public_key.write_to(&mut buf[o..]);
        o
    }

    pub fn read_from<R: Read>(mut r: R) -> std::io::Result<Self> {
        let endpoint = SecureUdpEndpoint::read_from(&mut r)?;
        let mut key_bytes = [0_u8; 32];
        r.read_exact(&mut key_bytes)?;
        Ok(EndpointEvidence { endpoint, root_public_key: key_bytes })
    }
}

fn fmt_byte_str(f: &mut std::fmt::Formatter<'_>, bytes: &[u8]) -> std::fmt::Result {
    let n = usize::min(bytes.len(), f.precision().unwrap_or(bytes.len()));
    for i in 0..n { write!(f, "{:02x}", bytes[i])?; }
    Ok(())
}

fn fmt_prefixed_byte_str(f: &mut std::fmt::Formatter<'_>, pre: &str, bytes: &[u8]) -> std::fmt::Result {
    write!(f, "{}", pre)?;
    fmt_byte_str(f, bytes)
}

impl std::fmt::Debug for StaticDHKeyPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_prefixed_byte_str(f, "StaticDHKeyPair { private: \"", &self.private)?;
        fmt_prefixed_byte_str(f, "\", public: \"",                &self.public)?;
        write!(f, "\" }}")
    }
}

impl std::fmt::Debug for EndpointEvidence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "EndpointEvidence {{ endpoint: ")?;
        self.endpoint.fmt(f)?;
        fmt_prefixed_byte_str(f, ", root_public_key: \"", &self.root_public_key)?;
        write!(f, "\" }}")
    }
}

impl std::fmt::Debug for SecureUdpEndpoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_prefixed_byte_str(f, "SecureUdpEndpoint { public_key: \"", &self.public_key)?;
        fmt_prefixed_byte_str(f, "\", ip_address: \"",                 &self.ip_address)?;
        write!(f, "\", port: {:05} }}", self.port)
    }
}

// returns true if a is initiator
fn contended_noise_is_initiator(hash_keys: &HashKeys, a: &[u8; 32], b: &[u8; 32]) -> bool {
    // TODO: do we want a fast insecure hash for this kind of thing?
    let a_to_b_hash = hash_keys.connect_contention.hasher().update(a).update(b).finalize();
    let b_to_a_hash = hash_keys.connect_contention.hasher().update(b).update(a).finalize();
    a_to_b_hash.as_bytes() <= b_to_a_hash.as_bytes()
}

fn nonce_is_ok2(nonce: u64, nonce_ack_latest: u64, nonce_ack_field: u64) -> bool {(
    nonce_ack_latest <= nonce + 64 && // TODO: do we want to completely drop these or just exclude from heartbeat
    nonce != nonce_ack_latest &&
    nonce <= nonce_ack_latest + NONCE_FORWARD_JUMP_TOLERANCE &&
    (nonce_ack_latest < nonce || nonce_ack_field >> (nonce_ack_latest - nonce) & 1 == 0)
)}

fn nonce_is_ok(nonce: u64, nonce_ack_latest: u64, nonce_ack_field: u64) -> bool {
    if nonce > nonce_ack_latest && nonce > nonce_ack_latest + NONCE_FORWARD_JUMP_TOLERANCE { return false; }
    if nonce == nonce_ack_latest                                                           { return false; }
    if nonce + 64 < nonce_ack_latest                                                       { return false; }
    // NOTE: this shift can overflow if we don't return before
    if nonce < nonce_ack_latest && nonce_ack_field >> (nonce_ack_latest - nonce) & 1 != 0  { return false; }
    true
}

fn nonce_update(nonce: u64, nonce_ack_latest: &mut u64, nonce_ack_field: &mut u64) {
    // Update nonce tracking
    if nonce > *nonce_ack_latest {
        *nonce_ack_latest += 1;
        *nonce_ack_field <<= 1;
        *nonce_ack_field |= 1;
        let shift_amount = nonce - *nonce_ack_latest;
        if shift_amount >= 64 {
            *nonce_ack_field = 0;
        } else if shift_amount != 0 {
            *nonce_ack_field <<= shift_amount;
            *nonce_ack_latest = nonce;
        }
    } else {
        *nonce_ack_field |= 1_u64 << (*nonce_ack_latest - nonce);
    }
}

/*
FROM ZEBRA
DATA LAYOUT FOR VOTE
32 byte ed25519 public key of the finalizer who's vote this is
32 byte blake3 hash of value, or all zeroes to indicate Nil vote
8 byte height
4 byte round where MSB is used to indicate is_commit for the vote type. 1 bit is_commit, 31 bits round index

TOTAL: 76 B

A signed vote will be this same layout followed by the 64 byte ed25519 signature of the previous 76 bytes.
*/

fn make_vote_sign_datas(pub_key: [u8; 32], is_precommit: bool, height: u64, round: u32, value_id: ValueId) -> [[u8; 76]; 2] {
    let mut sign_data_no = [0; 76];
    sign_data_no[0..32].copy_from_slice(&pub_key[..]);
    height.write_to(&mut sign_data_no[64..]);
    (round + 0x8000_0000 * (is_precommit as u32)).write_to(&mut sign_data_no[72..]);
    let mut sign_data_yes = sign_data_no;
    value_id.0.write_to(&mut sign_data_yes[32..64]);
    [sign_data_no, sign_data_yes]
}

pub fn gen_mostly_empty_rngs<F: Fn(usize) -> bool>(n: usize, f: F) -> Vec<[usize; 2]> {
    let mut rngs: Vec<[usize;2]> = Vec::with_capacity(n);
    let mut filled_c = 0; // consecutive fills
    let mut rng = [0, 0];
    // TODO(perf): these can be split arbitrarily & merged if we wanted to go wide
    for i in 0..n {
        if f(i) {
            rng[1] = i+1;
            filled_c = 0; // consecutive only, could also consider occupancy
        } else if rng[0] == rng[1] { // skip over leading fills
            rng[0] = i+1;
            rng[1] = i+1;
        } else {
            filled_c += 1;
            if filled_c > 1 { // 2 in a row
                rngs.push(rng);
                filled_c = 0;
                rng[0] = i+1;
                rng[1] = i+1;
            }
        }
    }
    if rng[0] != rng[1] {
        rngs.push(rng);
    }

    rngs
}

async fn instance(my_root_private_key: SigningKey, my_static_keypair: Option<StaticDHKeyPair>, my_endpoint: Option<SecureUdpEndpoint>, roster: Vec<SortedRosterMember>, roster_endpoint_evidence: Vec<EndpointEvidence>, maybe_seed: Option<u128>) -> std::io::Result<()> {
    let block_rng = Arc::new(Mutex::new({
        let seed : u128 = maybe_seed.clone().unwrap_or_else(||{
            let mut seed_rng = rand::rng();
            ((seed_rng.next_u64() as u128) << 64) | seed_rng.next_u64() as u128
        });
        SimRng::new(seed, 0)
    }));

    let should_propose_bad_value_sometimes = my_endpoint.is_some(); // peer 0 only

    let decisions = Arc::new(Mutex::new(Vec::<(BlockValue, FatPointerToBftBlock3)>::new()));
    let decisions2 = Arc::clone(&decisions);

    let roster2 = roster.clone();

    entry_point(my_root_private_key, my_static_keypair, my_endpoint, roster, roster_endpoint_evidence, maybe_seed,
        ClosureToProposeNewBlock(Arc::new(move || {
            let block_rng = Arc::clone(&block_rng);
            Box::pin(async move {
                let mut buf = vec![0; 6000]; // TODO: replace with real data
                block_rng.lock().unwrap().fill_bytes(&mut buf);
                if should_propose_bad_value_sometimes == false { buf[0] = 0; }
                Some(BlockValue(buf))
            })
        })),
        ClosureToValidateProposedBlock(Arc::new(move |block| {
            Box::pin(async move {
                if block.0.len() == 0 { TMStatus::Fail }
                else if block.0[0] % 2 == 0 { TMStatus::Pass }
                //else if block.0[0] % 3 == 1 { TMStatus::Indeterminate }
                else { TMStatus::Fail }
            })
        })),
        ClosureToPushDecidedBlock(Arc::new(move |block, fat_pointer| {
            let decisions = Arc::clone(&decisions);
            let roster2 = roster2.clone();
            Box::pin(async move {
                decisions.lock().unwrap().push((block, fat_pointer));
                let mut ret = roster2.clone();
                ret.truncate(3 + decisions.lock().unwrap().len() % 2);
                ret
            })
        })),
        ClosureToGetHistoricalBlock(Arc::new(move |height| {
            let decisions = Arc::clone(&decisions2);
            Box::pin(async move {
                decisions.lock().unwrap()[height as usize].clone()
            })
        }))
    ).await
}

pub async fn entry_point(my_root_private_key: SigningKey, my_static_keypair: Option<StaticDHKeyPair>, my_endpoint: Option<SecureUdpEndpoint>, mut roster: Vec<SortedRosterMember>, mut roster_endpoint_evidence: Vec<EndpointEvidence>, maybe_seed: Option<u128>, propose_closure: ClosureToProposeNewBlock, validate_closure: ClosureToValidateProposedBlock, push_block_closure: ClosureToPushDecidedBlock, get_block_closure: ClosureToGetHistoricalBlock) -> std::io::Result<()> {
    hook_fail_on_panic();
    let mut base_rng = {
        let seed : u128 = maybe_seed.unwrap_or_else(||{
            let mut seed_rng = rand::rng();
            ((seed_rng.next_u64() as u128) << 64) | seed_rng.next_u64() as u128
        });
        SimRng::new(seed, 0)
    };

    let noise_params: snow::params::NoiseParams = "Noise_IK_25519_ChaChaPoly_BLAKE2s".parse().unwrap();
    let my_root_public_key = VerificationKeyBytes::from(&my_root_private_key);
    let my_static_keypair = my_static_keypair.unwrap_or_else(|| {
        let kp = snow::Builder::new(noise_params.clone()).generate_keypair().unwrap();
        StaticDHKeyPair { private: kp.private.try_into().unwrap(), public: kp.public.try_into().unwrap(), }
    });

    let sock = {
        use socket2::{Domain, Protocol, Socket, Type};
        let socket = Socket::new(Domain::IPV6, Type::DGRAM, Some(Protocol::UDP)).unwrap();
        socket.set_nonblocking(true).unwrap();
        socket.set_only_v6(false).unwrap(); // Sets IPV6_V6ONLY to 0 for dual-stack (required for win32)
        socket.bind(&SocketAddrV6::new(Ipv6Addr::UNSPECIFIED, my_endpoint.map(|e|e.port).unwrap_or(0), 0, 0).into()).unwrap();
        tokio::net::UdpSocket::from_std(socket.into()).unwrap()
    };

    let my_port = sock.local_addr().unwrap().port();

    let mut peers : Vec<Peer> = roster.iter().filter(|m| m.pub_key.0 != my_root_public_key.as_ref())
        .map(|m| Peer { root_public_key: m.pub_key.0, ..Peer::default() }).collect();

    for evidence in &roster_endpoint_evidence {
        if let Some(i) = peers.iter().position(|p| p.root_public_key == evidence.root_public_key) {
            peers[i].endpoint = Some(evidence.endpoint);
        }
    }
    println!("socket port={:05}, peers endpoints={:?}", my_port, peers.iter().map(|p|p.endpoint).collect::<Vec<_>>());

    // TODO: only convert private to public in 1 location
    let mut bft_state = TMState::init(my_root_private_key, PubKeyID(my_root_public_key.into()), my_port, propose_closure, validate_closure, push_block_closure, get_block_closure); // TODO: double-check this is the right key
    bft_state.start_round(&roster, Instant::now(), 0).await;

    let mut my_endpoint_evidence = if let Some(i) = roster_endpoint_evidence.iter().position(|e| &e.root_public_key == my_root_public_key.as_ref()) {
        Some(roster_endpoint_evidence[i])
    } else {
        my_endpoint.map(|endpoint| EndpointEvidence { endpoint, root_public_key: my_root_public_key.into() })
    };

    let mut unknown_peers: Vec<UnknownPeer> = Vec::new();

    struct NetworkStats {
        bytes_sent: usize,
        packets_sent: usize,
    }

    let time_we_started_at = tokio::time::Instant::now();
    let mut net_stats = NetworkStats {
        bytes_sent: 0,
        packets_sent: 0,
    };

    let mut recv_buf1 = [0; 2048];
    let mut recv_buf2 = [0; 2048];
    let mut send_buf1 = [0; 2048];
    let mut send_buf2 = [0; 2048];
    let mut next_tick_time = tokio::time::Instant::now();
    loop {
        let ctx_str = bft_state.ctx_str(&roster);

        // @TodoHeaderAndStatus
        fn read_header_and_maybe_status(msg: &[u8]) -> std::io::Result<(PacketHeader, Option<PacketStatus>, usize)> {
            let mut o   = 0;
            let mut cur = Cursor::new(&msg[o..]);
            let header  = PacketHeader::read_from(&mut cur)?;

            let mut status = None;
            if (header.tag & PACKET_TAG_STATUS_FLAG) != 0 {
                // TODO: scope down required ranges
                status = Some(PacketStatus::read_from(&mut cur)?);
            }
            o += cur.position() as usize;
            Ok((header, status, o))
        }

        // @TodoHeaderAndStatus
        fn write_tag_and_maybe_status(packet_type: u8, include_status: bool, bft_state: &TMState, roster: &[SortedRosterMember], send_buf1: &mut [u8], peer_random: u64) -> usize {
            let packet_tag = packet_type | if include_status { PACKET_TAG_STATUS_FLAG } else { 0 }; // @TodoPacketHeader

            let mut o = 0;
            o += packet_tag.write_to(&mut send_buf1[o..]);

            if include_status {
                let mut status = PacketStatus {
                    height: bft_state.height,
                    round: bft_state.round,
                    need_proposal_chunk_rngs: [[0, 0]],
                    need_vote_rngs: [[[0, active_roster_len(roster) as u16]]; 2],
                };


                // TODO: scope down required ranges
                // TODO: probably generate these ranges once per tick/incrementally update & pull from it
                // TODO: weight by stake? (easily determined by cumulative stake)
                if let Ok(current_round_i) = bft_state.rounds_data.binary_search_by_key(&(status.height, status.round), |el| (el.height, el.round))
                {

                    let round_data = &bft_state.rounds_data[current_round_i];

                    let proposal_chunk_rngs = gen_mostly_empty_rngs(round_data.proposal_sigs.len(), |i| round_data.proposal_sigs[i] == TMSig::NIL);
                    if proposal_chunk_rngs.len() > 0 {
                        let mut random_i = peer_random;
                        for dst_rng in &mut status.need_proposal_chunk_rngs {
                            let rng = proposal_chunk_rngs[random_i as usize % proposal_chunk_rngs.len()];
                            *dst_rng = [rng[0].try_into().unwrap(), rng[1].try_into().unwrap()];
                            random_i = random_i.wrapping_add(1610612741); // large prime
                            // TODO: "with removal"
                        }
                    }
                    if PRINT_RNGS { println!("{} request proposal  chunks {:?} from {:?}", bft_state.ctx_str(roster), status.need_proposal_chunk_rngs, proposal_chunk_rngs); }

                    for is_precommit in 0..2 {
                        let vote_rngs = gen_mostly_empty_rngs(active_roster_len(roster), |i| round_data.msg_val_sigs[i][is_precommit].1 == TMSig::NIL);
                        if vote_rngs.len() > 0 {
                            let mut random_i = peer_random;
                            for dst_rng in &mut status.need_vote_rngs[is_precommit] {
                                let rng = vote_rngs[random_i as usize % vote_rngs.len()];
                                *dst_rng = [rng[0].try_into().unwrap(), rng[1].try_into().unwrap()];
                                random_i = random_i.wrapping_add(1610612741); // large prime
                                // TODO: "with removal"
                            }
                        }
                        if PRINT_RNGS { println!("{} request {:9} chunks {:?} from {:?}", bft_state.ctx_str(roster), ["prevote", "precommit"][is_precommit], status.need_vote_rngs[is_precommit], vote_rngs); }
                    }

                }

                o += status.write_to(&mut send_buf1[o..]);
            }
            o
        }
        fn send_sock_msg(ctx_str: &str, sock: &tokio::net::UdpSocket, peer_endpoint: SecureUdpEndpoint, msg: &[u8], stats: &mut NetworkStats) {
            // println!("Packet: {} bytes", msg.len());
            let addr = SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer_endpoint.ip_address), peer_endpoint.port, 0, 0));
            match sock.try_send_to(msg, addr) {
                Ok(_) => {
                    stats.packets_sent += 1;
                    stats.bytes_sent += msg.len();
                    ()
                },
                Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                Err(error) => panic!("{} Socket error: {:?} sending to addr: {:?}", ctx_str, error, addr),
            }
        }
        fn send_noise_msg(ctx_str: &str, transport: &mut StatelessTransportState, sock: &tokio::net::UdpSocket, peer_endpoint: SecureUdpEndpoint, on_send_next_nonce: &mut u64, send_buf2: &mut [u8], msg: &[u8], stats: &mut NetworkStats) {
            let mut o = 0;
            o += on_send_next_nonce.write_to(                               &mut send_buf2[o..]);
            o += transport         .write_message(*on_send_next_nonce, msg, &mut send_buf2[o..]).unwrap();
            send_sock_msg(ctx_str, sock, peer_endpoint, &send_buf2[..o], stats);

            *on_send_next_nonce += 1;
        }

        let was_now = tokio::time::Instant::now();
        if was_now > next_tick_time {
            loop {
                // TICK CODE
                unknown_peers.retain(|peer| {
                    if peer.watch_dog.elapsed() > TIMEOUT_DURATION {
                        println!("{:05}: Disconnected from unknown peer {:?}", my_port, peer.endpoint);
                        false
                    } else { true }
                });
                for peer in &mut peers {
                    if peer.watch_dog.elapsed() > TIMEOUT_DURATION {
                        if peer.transport_state.is_some() {
                            println!("{:05}: Disconnected from peer {:?}", my_port, peer.endpoint);
                        }
                        peer.outgoing_handshake_state           = None;
                        peer.pending_client_ack_transport_state = None;
                        peer.transport_state                    = None;
                        peer.watch_dog                          = Instant::now();
                    }

                    if let (Some(peer_endpoint), Some(transport)) = (peer.endpoint, &mut peer.transport_state) {
                        if peer.connection_is_unknown {
                            // Gossip evidence in order to trigger upgrade
                            if let Some(evidence) = my_endpoint_evidence {
                                let header = PacketHeader::new::<PACKET_TYPE_ENDPOINT_EVIDENCE>(peer.nonce_ack_latest, peer.nonce_ack_field);
                                let mut o  = 0;
                                o += header  .write_to(&mut send_buf1[o..]); // @TodoHeaderAndStatus
                                o += evidence.write_to(&mut send_buf1[o..]);
                                send_noise_msg(&ctx_str, transport, &sock, peer_endpoint, &mut peer.on_send_next_nonce, &mut send_buf2, &send_buf1[..o], &mut net_stats);
                            }
                        } else {
                            let mut o = 0; // @TodoPacketHeader
                            o += write_tag_and_maybe_status(PACKET_TYPE_EMPTY, true, &bft_state, &roster, &mut send_buf1[..], peer.on_send_next_nonce);
                            send_noise_msg(&ctx_str, transport, &sock, peer_endpoint, &mut peer.on_send_next_nonce, &mut send_buf2, &send_buf1[..o], &mut net_stats);
                        }
                    }
                }
                for peer in &mut peers {
                    if let Some(peer_endpoint) = peer.endpoint {
                        if peer.transport_state.is_none() && peer.outgoing_handshake_state.is_none() && peer.pending_client_ack_transport_state.is_none() {
                            let mut outgoing_state: HandshakeState = snow::Builder::new(noise_params.clone())
                                .local_private_key(&my_static_keypair.private).unwrap()
                                .remote_public_key(&peer_endpoint.public_key).unwrap()
                                .build_initiator().unwrap();
                            let header = PacketHeader::new::<PACKET_TYPE_CLIENT_HELLO>(peer.nonce_ack_latest, peer.nonce_ack_field);
                            let mut o = 0;
                            o += header.write_to(&mut send_buf1[o..]); // @TodoHeaderAndStatus
                            let n = outgoing_state.write_message(&send_buf1[..o], &mut send_buf2).unwrap();
                            // TODO: no nonce?
                            send_sock_msg(&ctx_str, &sock, peer_endpoint, &send_buf2[..n], &mut net_stats);
                            peer.outgoing_handshake_state = Some(outgoing_state);
                        }

                        if let (Some(transport), Some(evidence)) =
                            (&mut peer.transport_state, roster_endpoint_evidence.choose(&mut base_rng)) {
                            let header = PacketHeader::new::<PACKET_TYPE_ENDPOINT_EVIDENCE>(peer.nonce_ack_latest, peer.nonce_ack_field);
                            let mut o = 0;
                            o += header  .write_to(&mut send_buf1[o..]); // @TodoHeaderAndStatus
                            o += evidence.write_to(&mut send_buf1[o..]);
                            send_noise_msg(&ctx_str, transport, &sock, peer_endpoint, &mut peer.on_send_next_nonce, &mut send_buf2, &send_buf1[..o], &mut net_stats);
                        }
                    }
                }

                // BFT CONSENSUS
                // account for the state updates we've accumulated
                bft_state.bft_update(&mut roster).await;

                fn send_round_data_to_peer(bft_state: &TMState, should_send_prevotes: bool, round_data: &RoundData, ctx_str: &str, send_buf1: &mut [u8], send_buf2: &mut [u8], peer: &mut Peer, sock: &tokio::net::UdpSocket, stats: &mut NetworkStats) {
                    let height = round_data.height;
                    let round  = round_data.round;

                    let mut chunk_hdr = PacketProposalChunkHeader {
                        height, round, chunk_i: 0,
                        proposal_size: round_data.proposal.0.len().try_into().unwrap(),
                        proposal_id: round_data.proposal_id,
                        valid_round: round_data.proposal_valid_round,
                    };
                    let (_, proposer_pub_key) = TMState::proposer_from_height_round(&bft_state.hash_keys, &round_data.roster, height, round);

                    let mut sent_chunk_cs = 0;
                    let mut sent_c: [usize; 2] = [0; 2];

                    if round_data.proposal_sigs_n > 0 {
                        for chunk_i in 0..round_data.proposal_sigs.len() {
                            // send all of the proposal chunks we've seen
                            if round_data.proposal_sigs[chunk_i] != TMSig::NIL {
                                chunk_hdr.chunk_i = chunk_i as u32;

                                let header = PacketHeader::new::<PACKET_TYPE_PROPOSAL_CHUNK>(peer.nonce_ack_latest, peer.nonce_ack_field);

                                let mut o = 0;
                                o += header   .write_to(&mut send_buf1[o..]); // @TodoHeaderAndStatus
                                o += chunk_hdr.write_to(&mut send_buf1[o..]);

                                let (chunk_o, chunk_size) = round_data.proposal.chunk_o_size(chunk_i);
                                o += round_data.proposal.0[chunk_o..chunk_o + chunk_size].write_to(&mut send_buf1[o..]);
                                let sig_o = o;
                                o += round_data.proposal_sigs[chunk_i].0.write_to(&mut send_buf1[o..]);

                                #[cfg(debug_assertions)]
                                { // self-check signatures as sanity check
                                    let sig = Signature::from_bytes(&round_data.proposal_sigs[chunk_i].0);
                                    let vk = match VerificationKey::try_from(proposer_pub_key.0) { Ok(v)=>v, Err(err)=>{
                                        eprintln!("{}: BFT FAULT: invalid proposal public key: {} ({})", ctx_str, proposer_pub_key, err);
                                        continue;
                                    }};
                                    match vk.verify(&sig, &send_buf1[1..sig_o]) { Ok(_)=>{}, Err(err)=>{
                                        eprintln!("{}: BFT FAULT: invalid signature from {} for proposal {}.{}.{}[..{}]: {} {}",
                                            ctx_str, proposer_pub_key, height, round, chunk_i, sig_o-1, chunk_hdr.proposal_id, err);
                                        continue;
                                    }}
                                }

                                if let (Some(peer_endpoint), Some(transport)) = (peer.endpoint, &mut peer.transport_state) {
                                    if PRINT_SENDS { eprintln!("{} sending proposal chunk {} to {:?}", ctx_str, chunk_i, peer.root_public_key); }

                                    sent_chunk_cs += 1;
                                    send_noise_msg(&ctx_str, transport, &sock, peer_endpoint, &mut peer.on_send_next_nonce, send_buf2, &mut send_buf1[..o], stats);
                                }
                            }
                        }
                    }

                    let vote_start: u8 = if should_send_prevotes { 0 } else { 1 };
                    for is_precommit in vote_start..2 {
                        if  (is_precommit == 0 && round_data.counts.prevotes   == 0) ||
                            (is_precommit == 1 && round_data.counts.precommits == 0)
                        {
                            continue;
                        }

                        let header = PacketHeader::new_(PACKET_TYPE_PREVOTE_SIGNATURES + is_precommit, peer.nonce_ack_latest, peer.nonce_ack_field); // TODO: maybe include status
                        let mut packet = PacketVotes {
                            height, round,
                            value_id: chunk_hdr.proposal_id,
                            no_votes_n: 0, yes_votes_n: 0,
                            votes: [ PubKeySig::NIL; 18 ],
                        };

                        for roster_i in 0..round_data.msg_val_sigs.len() {
                            let (value_id, sig) = round_data.msg_val_sigs[roster_i][is_precommit as usize];
                            if sig != TMSig::NIL {
                                let pub_key_sig = PubKeySig{ roster_i: roster_i.try_into().unwrap(), sig };
                                // println!("{} {}: packing in sig from {}", ctx_str, PubKeyID(my_root_public_key.into()), pub_key_sig.pub_key);

                                // add nos and yeses from opposite ends to avoid excess moves
                                if value_id == ValueId::NIL {
                                    packet.votes[packet.no_votes_n as usize] = pub_key_sig;
                                    packet.no_votes_n += 1;
                                } else {
                                    packet.yes_votes_n += 1; // *intentionally* pre-decrement because we're indexing from end
                                    packet.votes[packet.votes.len() - packet.yes_votes_n as usize] = pub_key_sig;
                                };

                                if (packet.no_votes_n + packet.yes_votes_n) as usize == packet.votes.len() {
                                    sent_c[is_precommit as usize] += (packet.no_votes_n + packet.yes_votes_n) as usize;
                                    // full evidence block; send it
                                    if PRINT_SENDS { println!("{}: sending full {} block: {:#?}", ctx_str, ["prevote", "precommit"][is_precommit as usize], packet); }
                                    // TODO: maybe status
                                    let mut o = 0;
                                    o += header.write_to(&mut send_buf1[o..]); // @TodoHeaderAndStatus
                                    o += packet.write_to(&mut send_buf1[o..]);
                                    if let (Some(peer_endpoint), Some(transport)) = (peer.endpoint, &mut peer.transport_state) {
                                        send_noise_msg(&ctx_str, transport, &sock, peer_endpoint, &mut peer.on_send_next_nonce, send_buf2, &mut send_buf1[..o], stats);
                                    }

                                    packet.no_votes_n  = 0;
                                    packet.yes_votes_n = 0;
                                    packet.votes       = [PubKeySig::NIL; 18];
                                }
                            }
                        }

                        // send any half-filled vote blocks
                        if (packet.no_votes_n + packet.yes_votes_n) > 0 {
                            sent_c[is_precommit as usize] += (packet.no_votes_n + packet.yes_votes_n) as usize;
                            // println!("{}: half-filled block pre-gap-close: {:#?}", ctx_str, packet);
                            // move items from end to fill gap
                            for gap_i in 0..packet.votes.len() - (packet.no_votes_n + packet.yes_votes_n) as usize {
                                packet.votes[packet.no_votes_n as usize + gap_i] = packet.votes[packet.votes.len() - 1 - gap_i];
                            }

                            if PRINT_SENDS { println!("{}: half-filled block post-gap-close: {:#?}", ctx_str, packet); }

                            let mut o = 0;
                            o += header.write_to(&mut send_buf1[o..]); // @TodoHeaderAndStatus
                            o += packet.write_to(&mut send_buf1[o..]);
                            // TODO: maybe status
                            if let (Some(peer_endpoint), Some(transport)) = (peer.endpoint, &mut peer.transport_state) {
                                send_noise_msg(&ctx_str, transport, &sock, peer_endpoint, &mut peer.on_send_next_nonce, send_buf2, &send_buf1[..o], stats);
                            }
                        }
                    }

                    if PRINT_SEND_CS && sent_chunk_cs > 0 {
                        eprintln!("{} sent {} proposal chunks", ctx_str, sent_chunk_cs);
                    }

                    if PRINT_SEND_CS && sent_c[0] > 0 {
                        println!("{} sent {} prevotes", ctx_str, sent_c[0]);
                    }
                    if PRINT_SEND_CS && sent_c[1] > 0 {
                        println!("{} sent {} precommits", ctx_str, sent_c[1]);
                    }
                }

                if PRINT_PEERS { println!("{} {:?}", ctx_str, peers.iter().map(|p|
                    (PubKeyID(p.root_public_key), p.latest_status.clone(), p.connection_is_unknown)
                ).collect::<Vec<_>>()); }

                for peer_i in 0..peers.len() {
                    let peer = &mut peers[peer_i];
                    if let Some(height) = peer.unacted_upon_status_height && height < bft_state.height {
                        peer.unacted_upon_status_height = None;
                        send_round_data_to_peer(&bft_state, false, &bft_state.recent_commit_round_cache[height as usize], &ctx_str, &mut send_buf1, &mut send_buf2, peer, &sock, &mut net_stats);
                    }
                    else if let Ok(current_height_start_i) = bft_state.rounds_data.binary_search_by_key(&(bft_state.height, 0), |el| (el.height, el.round))
                    {
                        for round_i in current_height_start_i..bft_state.rounds_data.len()
                        {
                            let round_data = &bft_state.rounds_data[round_i];
                            send_round_data_to_peer(&bft_state, true, &round_data, &ctx_str, &mut send_buf1, &mut send_buf2, peer, &sock, &mut net_stats);
                        }
                    } else {
                        eprintln!("{}: \x1b[91mBFT ERROR\x1b[0m: round_data array was empty", ctx_str);
                    }
                }

                if PRINT_NETWORK_STATS {
                    let elapsed = time_we_started_at.elapsed();
                    let nonzero_elapsed_sec = if (elapsed.is_zero()) { 1f32 } else { elapsed.as_secs_f32() };

                    let kbps = (std::cmp::max(1, net_stats.bytes_sent)   as f32) / 1000.0 / (nonzero_elapsed_sec);
                    let  pps = (std::cmp::max(1, net_stats.packets_sent) as f32)          / (nonzero_elapsed_sec);
                    let  bpp = (std::cmp::max(1, net_stats.bytes_sent)   as f32)          / (std::cmp::max(1, net_stats.packets_sent) as f32);

                    println!("\x1b[92mNET\x1b[0m: SENT {} b, {} pckts ({} Kb/s {} pckts/s, {} b/pckt)",
                             net_stats.bytes_sent, net_stats.packets_sent,
                             kbps, pps, bpp);
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
            Ok(Ok(ret)) => ret,
        };
        if length < 8 { continue; } // early out to simplify nonce code
        let raw_msg = &recv_buf1[..length];

        let from_ip = match addr {
            SocketAddr::V4(v4) => v4.ip().to_ipv6_mapped().octets(),
            SocketAddr::V6(v6) => v6.ip().octets(),
        };
        let from_port = addr.port();

        // DECRYPT
        let mut peer_index = 0;
        let mut peer_is_unknown = false;
        let mut nonce = 0;
        let mut msg: Option<&[u8]> = None;

        //  NOTE(Security): Actually we would need to loop because a peer could sign a message claiming to own an IP and PORT that it actually does not own. That also means falling back on
        //      the unknown connections array since that also shouldn't be able to be blocked.
        if let Some(i) = peers.iter().map(|p| p.endpoint.unwrap_or_default()).position(|endpoint| endpoint.ip_address == from_ip && endpoint.port == from_port) {
            let peer_endpoint = peers[i].endpoint.unwrap();
            loop {
                let peer = &mut peers[i];
                if let Some(transport) = &mut peer.transport_state {
                    nonce = u64::from_le_bytes(raw_msg[0..8].try_into().unwrap());
                    if let Ok(length) = transport.read_message(nonce, &raw_msg[8..], &mut recv_buf2) {
                        if nonce_is_ok(nonce, peer.nonce_ack_latest, peer.nonce_ack_field) {
                            msg        = Some(&recv_buf2[0..length]);
                            peer_index = i;
                        }
                        break;
                    }
                }
                if let Some(outgoing) = &mut peer.outgoing_handshake_state {
                    if let Ok(length) = outgoing.read_message(raw_msg, &mut recv_buf2) {
                        fn finish_outgoing_handshake(ctx_str: &str, send_buf2: &mut [u8], sock: &tokio::net::UdpSocket, peer_endpoint: SecureUdpEndpoint, peer: &mut Peer, mut transport: StatelessTransportState, nonce: u64, connection_is_unknown: bool, stats: &mut NetworkStats) {
                            // @TodoPacketHeader
                            let packet_type = if connection_is_unknown { PACKET_TYPE_CLIENT_UNKNOWN_ACK } else { PACKET_TYPE_CLIENT_ACK };

                            // TODO: we should rate-limit new connections so adversaries can't exhaust your entropy pool by rapidly asking for new nonces
                            peer.on_send_next_nonce = rand::random::<u64>() >> (PACKET_TYPE_BITS + 1);

                            send_noise_msg(ctx_str, &mut transport, sock, peer_endpoint, &mut peer.on_send_next_nonce, send_buf2, &[packet_type], stats);

                            peer.transport_state                    = Some(transport);
                            peer.outgoing_handshake_state           = None;
                            peer.pending_client_ack_transport_state = None;
                            peer.nonce_ack_latest                   = nonce;
                            peer.nonce_ack_field                    = !0;
                            peer.connection_is_unknown              = connection_is_unknown;
                        }

                        if length <= 8 {
                            break; // presumably we don't care about standalone nonces
                        } else {
                            nonce = u64::from_le_bytes(recv_buf2[..8].try_into().unwrap());
                            let local_msg = &recv_buf2[8..length];
                            if local_msg == [PACKET_TYPE_SERVER_HELLO] /* @TodoPacketHeader */ {
                                if peer.pending_client_ack_transport_state.is_none() || !contended_noise_is_initiator(&bft_state.hash_keys, &my_root_public_key.into(), &peer.root_public_key) {
                                    if let Ok(transport) = peer.outgoing_handshake_state.take().unwrap().into_stateless_transport_mode() {
                                        println!("{:05}: Finished outgoing handshake and got nonce {} with {}", my_port, nonce, addr);
                                        finish_outgoing_handshake(&ctx_str, &mut send_buf2, &sock, peer_endpoint, peer, transport, nonce, false, &mut net_stats);
                                    }
                                    break;
                                }
                            } else if local_msg.len() == PACKET_HEADER_SIZE /* @TodoPacketHeader */ + 18 && local_msg[0] == PACKET_TYPE_SERVER_UNKNOWN_HELLO {
                                let other_side_ip       = &local_msg[PACKET_HEADER_SIZE     ..PACKET_HEADER_SIZE + 16];
                                let other_side_port     = &local_msg[PACKET_HEADER_SIZE + 16..PACKET_HEADER_SIZE + 18];
                                let other_side_endpoint = SecureUdpEndpoint { ip_address: other_side_ip.try_into().unwrap(), port: u16::from_le_bytes(other_side_port.try_into().unwrap()), public_key: my_static_keypair.public };
                                // TODO hash
                                if let Ok(transport) = peer.outgoing_handshake_state.take().unwrap().into_stateless_transport_mode() {
                                    println!("{:05}: Finished outgoing unknown handshake and got nonce {} with {}, I am percieved as {:?}", my_port, nonce, addr, other_side_endpoint);

                                    if my_endpoint_evidence.is_none() {
                                        let evidence = EndpointEvidence { endpoint: other_side_endpoint, root_public_key: my_root_public_key.into() };
                                        println!("{:05}: I am locking in the endpoint evidence {:?}", my_port, evidence);
                                        my_endpoint_evidence = Some(evidence);
                                    }

                                    finish_outgoing_handshake(&ctx_str, &mut send_buf2, &sock, peer_endpoint, peer, transport, nonce, true, &mut net_stats);
                                }
                                break;
                            }
                        }
                    }
                }
                if let Some(incoming) = &mut peer.pending_client_ack_transport_state {
                    nonce = u64::from_le_bytes(raw_msg[0..8].try_into().unwrap());
                    if let Ok(length) = incoming.read_message(nonce, &raw_msg[8..], &mut recv_buf2) {
                        let local_msg = &recv_buf2[..length];
                        if local_msg == [PACKET_TYPE_CLIENT_ACK] /* @TodoPacketHeader */ {
                            println!("{:05}: Finished incoming handshake and got nonce {} with {}", my_port, nonce, addr);
                            peer.transport_state          = peer.pending_client_ack_transport_state.take();
                            peer.outgoing_handshake_state = None;
                            peer.nonce_ack_latest         = nonce;
                            peer.nonce_ack_field          = !0;
                            peer.connection_is_unknown    = false;
                            break;
                        }
                    }
                }
                let mut incoming_state: HandshakeState = snow::Builder::new(noise_params.clone())
                    .local_private_key(&my_static_keypair.private).unwrap()
                    .build_responder().unwrap();
                if let Ok(length) = incoming_state.read_message(raw_msg, &mut recv_buf2) {
                    let local_msg = &recv_buf2[..length];
                    if local_msg == &[PACKET_TYPE_CLIENT_HELLO] /* @TodoPacketHeader */ {
                        let client_endpoint = SecureUdpEndpoint { public_key: incoming_state.get_remote_static().unwrap().try_into().unwrap(), ip_address: from_ip, port: from_port };
                        println!("{:05}: Server recieved client hello from static key = {:?}", my_port, client_endpoint);
                        if peer.outgoing_handshake_state.is_none() || contended_noise_is_initiator(&bft_state.hash_keys, &my_root_public_key.into(), &peer.root_public_key) {

                            // TODO: we should rate-limit new connections so adversaries can't exhaust your entropy pool by rapidly asking for new nonces
                            let start_nonce = rand::random::<u64>() >> (PACKET_TYPE_BITS + 1);

                            let mut o = 0;
                            o += start_nonce             .write_to(&mut send_buf1[o..]);
                            o += PACKET_TYPE_SERVER_HELLO.write_to(&mut send_buf1[o..]);

                            let n = incoming_state.write_message(&send_buf1[..o], &mut send_buf2).unwrap();
                            send_sock_msg(&ctx_str, &sock, peer_endpoint, &send_buf2[..n], &mut net_stats);

                            if let Ok(transport) = incoming_state.into_stateless_transport_mode() {
                                peer.pending_client_ack_transport_state = Some(transport);
                                peer.on_send_next_nonce                 = start_nonce+1;
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
                            if local_msg == [PACKET_TYPE_CLIENT_UNKNOWN_ACK] {
                                println!("{:05}: Finished incoming unknown handshake and got nonce {} with {}", my_port, nonce, addr);
                                peer.pending_client_ack = false;
                                peer.nonce_ack_latest   = nonce;
                                peer.nonce_ack_field    = !0;
                                break;
                            }
                            break;
                        }

                        if nonce_is_ok(nonce, peer.nonce_ack_latest, peer.nonce_ack_field) {
                            msg             = Some(&recv_buf2[0..length]);
                            peer_index      = i;
                            peer_is_unknown = true;
                        }
                        break;
                    }
                }
                let mut incoming_state: HandshakeState = snow::Builder::new(noise_params.clone())
                    .local_private_key(&my_static_keypair.private).unwrap()
                    .build_responder().unwrap();
                if let Ok(length) = incoming_state.read_message(raw_msg, &mut recv_buf2) {
                    let local_msg = &recv_buf2[0..length];
                    if local_msg == [PACKET_TYPE_CLIENT_HELLO] {
                        let client_endpoint = SecureUdpEndpoint { public_key: incoming_state.get_remote_static().unwrap().try_into().unwrap(), ip_address: from_ip, port: from_port };
                        println!("{:05}: Server recieved client hello from unknown peer with static key = {:?}", my_port, client_endpoint);

                        // TODO: we should rate-limit new connections so adversaries can't exhaust your entropy pool by rapidly asking for new nonces
                        let start_nonce = rand::random::<u64>() >> (PACKET_TYPE_BITS + 1);

                        let mut o = 0;
                        o += start_nonce                     .write_to(&mut send_buf1[o..]);
                        o += PACKET_TYPE_SERVER_UNKNOWN_HELLO.write_to(&mut send_buf1[o..]);
                        o += from_ip                         .write_to(&mut send_buf1[o..]);
                        o += from_port                       .write_to(&mut send_buf1[o..]);

                        let n = incoming_state.write_message(&send_buf1[..o], &mut send_buf2).unwrap();
                        send_sock_msg(&ctx_str, &sock, client_endpoint, &send_buf2[..n], &mut net_stats);

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
        let msg: &[u8] = msg.unwrap();
        if msg.len() == 0 { continue; }
        let Ok((header, status, read_o)) = read_header_and_maybe_status(&msg[..]) else {
            continue;
        };
        let packet_type = header.tag & PACKET_TYPE_MASK;

        if peer_is_unknown {
            let peer = &mut unknown_peers[peer_index];
            peer.watch_dog = Instant::now();
            nonce_update(nonce, &mut peer.nonce_ack_latest, &mut peer.nonce_ack_field);

            match packet_type {
                PACKET_TYPE_ENDPOINT_EVIDENCE => match EndpointEvidence::read_from(&msg[read_o..]) {
                    Ok(evidence) => if let Some(i) = peers.iter().position(|p| p.root_public_key == evidence.root_public_key) {
                        peers[i].endpoint = Some(evidence.endpoint);
                        if peer.endpoint == evidence.endpoint {
                            println!("{:05}: Promoting unknown peer connection {:?}", my_port, peer.endpoint);
                            let peer = unknown_peers.remove(peer_index);
                            peers[i].outgoing_handshake_state           = None;
                            peers[i].pending_client_ack_transport_state = None;
                            peers[i].transport_state                    = Some(peer.transport_state);
                            peers[i].watch_dog                          = Instant::now();
                            peers[i].nonce_ack_latest                   = peer.nonce_ack_latest;
                            peers[i].nonce_ack_field                    = peer.nonce_ack_field;
                            peers[i].on_send_next_nonce                 = peer.on_send_next_nonce;
                            peers[i].connection_is_unknown              = false;
                        }
                        roster_endpoint_evidence.retain(|e| e.root_public_key != evidence.root_public_key);
                        roster_endpoint_evidence.push(evidence);
                    }
                    Err(err) => eprintln!("{:05}: couldn't read endpoint evidence: {}", my_port, err),
                }
                _ => println!("{:05}:  From unknown peer!   field={:016X} Got '{:?}' from {}", my_port, peer.nonce_ack_field, msg, addr),
            }
            continue;
        }

        else {
            let peer = &mut peers[peer_index];
            peer.watch_dog = Instant::now();
            nonce_update(nonce, &mut peer.nonce_ack_latest, &mut peer.nonce_ack_field);

            // TODO: other TAGs should also cause this transition
            if let Some(status) = status {
                if peer.connection_is_unknown {
                    println!("{:05}: Got a status, this means that the other side does not consider me unknown anymore!", my_port);
                    peer.connection_is_unknown = false;
                }

                peer.unacted_upon_status_height = Some(status.height);
                peer.latest_status = Some(status);
            }

            const_assert!(PACKET_TYPE_PREVOTE_SIGNATURES + 1 == PACKET_TYPE_PRECOMMIT_SIGNATURES);
            match packet_type {
                PACKET_TYPE_ENDPOINT_EVIDENCE => match EndpointEvidence::read_from(&msg[read_o..]) {
                    Ok(evidence) => if let Some(i) = peers.iter().position(|p| p.root_public_key == evidence.root_public_key) {
                        peers[i].endpoint = Some(evidence.endpoint);
                        roster_endpoint_evidence.retain(|e| e.root_public_key != evidence.root_public_key);
                        roster_endpoint_evidence.push(evidence);
                    }
                    Err(err) => eprintln!("{:05}: couldn't read endpoint evidence: {}", my_port, err),
                }

                PACKET_TYPE_PROPOSAL_CHUNK => {
                    let hdr = match PacketProposalChunkHeader::read_from(&msg[read_o..]) { Ok(v)=>v, Err(err)=>{
                        eprintln!("{:05}: couldn't read proposal header: {}", my_port, err);
                        continue;
                    }};
                    let proposal_size = hdr.proposal_size as usize;
                    let chunk_i       = hdr.chunk_i       as usize;
                    let chunk_size = usize::min(PROPOSAL_CHUNK_DATA_SIZE, proposal_size - chunk_i * PROPOSAL_CHUNK_DATA_SIZE);
                    let packet_size = chunk_size + PROPOSAL_PACKET_EXTRA;

                    // NOTE: assume for the moment that this is the valid height, we'll check in the subsequent call
                    // ALT:  cache proposer for *current* round
                    if msg.len() == packet_size {
                        if let (Some(roster_i), _) = TMState::proposer_from_height_round(&bft_state.hash_keys, &roster, hdr.height, hdr.round) {
                            let sig_o = 1 /* @TodoPacketHeader */ + PacketProposalChunkHeader::SERIALIZED_SIZE + chunk_size;
                            bft_state.check_and_incorporate_msg(hdr.height, hdr.round, hdr.chunk_i as usize, hdr.proposal_id, hdr.valid_round,
                                &roster, roster_i, packet_type, &msg[read_o..sig_o], &msg[sig_o..sig_o+64].try_into().unwrap());
                        }
                    } else {
                        eprintln!("{:05}: couldn't read proposal chunk: incorrect size {}", my_port, msg.len());
                    }
                }

                PACKET_TYPE_PREVOTE_SIGNATURES | PACKET_TYPE_PRECOMMIT_SIGNATURES => match PacketVotes::read_from(&msg[read_o..]) {
                    Ok(packet) => {
                        let is_precommit = packet_type - PACKET_TYPE_PREVOTE_SIGNATURES;
                        let value_ids    = [ ValueId::NIL, packet.value_id ];

                        for vote_i in 0..(packet.no_votes_n + packet.yes_votes_n) as usize {
                            // Note(Sam): We can change the format of votes to be cool and branchless after the workshop.
                            if let Some(roster_member) = roster.get(packet.votes[vote_i].roster_i as usize) {
                                let sign_datas   = make_vote_sign_datas(roster_member.pub_key.0, is_precommit != 0, packet.height, packet.round, packet.value_id);
                                let no_yes_i = (vote_i >= packet.no_votes_n as usize) as usize;
                                bft_state.check_and_incorporate_msg(packet.height, packet.round, 0, value_ids[no_yes_i], -2,
                                    &roster, packet.votes[vote_i].roster_i as usize, packet_type, &sign_datas[no_yes_i], &packet.votes[vote_i].sig.0);
                            }
                        }
                    }
                    Err(err) => eprintln!("{:05}: couldn't read {}: {}", my_port, packet_name_from_type(packet_type), err),
                }

                PACKET_TYPE_EMPTY => {}
                _ => {} // println!("{}:  From known peer!   field={:016X} Got '{:?}' from {}", my_port, peer.nonce_ack_field, msg, addr);
            }
            continue;
        }
    }
}

// network
const PACKET_TYPE_EMPTY                : u8 =  0;
const PACKET_TYPE_CLIENT_HELLO         : u8 =  1;
const PACKET_TYPE_CLIENT_UNKNOWN_ACK   : u8 =  2;
const PACKET_TYPE_CLIENT_ACK           : u8 =  3;
const PACKET_TYPE_SERVER_UNKNOWN_HELLO : u8 =  4;
const PACKET_TYPE_SERVER_HELLO         : u8 =  5;
const PACKET_TYPE_ENDPOINT_EVIDENCE    : u8 =  6;
// consensus
const PACKET_TYPE_PROPOSAL_CHUNK       : u8 =  7;
const PACKET_TYPE_PREVOTE_SIGNATURES   : u8 =  8;
const PACKET_TYPE_PRECOMMIT_SIGNATURES : u8 =  9;
const PACKET_TYPE_COUNT                : u8 = 10;


const PACKET_TYPE_BITS                 : u8 =  7;
const PACKET_TYPE_MASK                 : u8 = (1 << PACKET_TYPE_BITS) - 1;

const PACKET_TAG_STATUS_SHIFT          : u8 = PACKET_TYPE_BITS;
const PACKET_TAG_STATUS_FLAG           : u8 = 1 << PACKET_TAG_STATUS_SHIFT;

const PACKET_TAG_BITS                  : u8 = 8;
const PACKET_TAG_MASK                  : u8 = ((1 << PACKET_TAG_BITS as u64) - 1) as u8;


const PACKET_TYPE_NAMES: [[&str; 2]; PACKET_TYPE_COUNT as usize] = {
    let mut names = [["<MISSING>"; 2]; PACKET_TYPE_COUNT as usize];
    names[PACKET_TYPE_EMPTY                as usize] = ["<EMPTY>",              "STATUS"];
    names[PACKET_TYPE_CLIENT_HELLO         as usize] = ["CLIENT_HELLO",         "STATUS+CLIENT_HELLO"];
    names[PACKET_TYPE_CLIENT_UNKNOWN_ACK   as usize] = ["CLIENT_UNKNOWN_ACK",   "STATUS+CLIENT_UNKNOWN_ACK"];
    names[PACKET_TYPE_CLIENT_ACK           as usize] = ["CLIENT_ACK",           "STATUS+CLIENT_ACK"];
    names[PACKET_TYPE_SERVER_UNKNOWN_HELLO as usize] = ["SERVER_UNKNOWN_HELLO", "STATUS+SERVER_UNKNOWN_HELLO"];
    names[PACKET_TYPE_SERVER_HELLO         as usize] = ["SERVER_HELLO",         "STATUS+SERVER_HELLO"];
    names[PACKET_TYPE_ENDPOINT_EVIDENCE    as usize] = ["ENDPOINT_EVIDENCE",    "STATUS+ENDPOINT_EVIDENCE"];
    names[PACKET_TYPE_PROPOSAL_CHUNK       as usize] = ["PROPOSAL_CHUNK",       "STATUS+PROPOSAL_CHUNK"];
    names[PACKET_TYPE_PREVOTE_SIGNATURES   as usize] = ["PREVOTE_SIGNATURES",   "STATUS+PREVOTE_SIGNATURES"];
    names[PACKET_TYPE_PRECOMMIT_SIGNATURES as usize] = ["PRECOMMIT_SIGNATURES", "STATUS+PRECOMMIT_SIGNATURES"];
    const_assert!(PACKET_TYPE_COUNT == 10); // keep names array updated when adding other tags
    names
};
fn packet_name_from_type(packet_type: u8) -> &'static str {
    PACKET_TYPE_NAMES.get(packet_type as usize).unwrap_or(&["<UNKNOWN>", "STATUS+<UNKNOWN>"])[(packet_type >> PACKET_TAG_STATUS_SHIFT & 1) as usize]
}

// NOTE(azmr): could add packet sizes so we can check all sizes in 1 location

// ALT: if we limit to u16 chunk indexes & have ~1KB chunk data per packet, we could have block sizes up to ~65MB
// N.B. with ranges like this, we either want to be half-exclusive & not allow type::MAX values, or use a special value for empty (e.g. hi < lo)
type ProposalRng = [u32; 2]; // [lo, hi)
type VoteRng     = [u16; 2];
const STATUS_PROPOSAL_RNGS_N: usize = 1;
const STATUS_VOTE_RNGS_N: usize = 1; // ALT: split prevote/precommit numbers
#[derive(Clone, Debug)]
struct PacketStatus {
    height: u64,
    round:  u32, // as context for following request ranges
    need_proposal_chunk_rngs: [ProposalRng; STATUS_PROPOSAL_RNGS_N],
    need_vote_rngs: [[VoteRng; STATUS_VOTE_RNGS_N]; 2], // 1 for prevote, 1 for precommit
}
impl PacketStatus {
    pub fn write_to(&self, buf: &mut[u8]) -> usize {
        let mut o = 0;
        o += self.height.write_to(&mut buf[o..]);
        o += self.round .write_to(&mut buf[o..]);
        for chunk_rng in &self.need_proposal_chunk_rngs {
            o += chunk_rng[0].write_to(&mut buf[o..]);
            o += chunk_rng[1].write_to(&mut buf[o..]);
        }
        for is_precommit in 0..2 {
            for vote_rng in &self.need_vote_rngs[is_precommit] {
                o += vote_rng[0].write_to(&mut buf[o..]);
                o += vote_rng[1].write_to(&mut buf[o..]);
            }
        }
        o
    }

    pub fn read_from<R: Read>(mut r: R) -> std::io::Result<Self> {
        let mut packet = Self {
            height: 0, round: 0,
            need_proposal_chunk_rngs: [[0;2]; STATUS_PROPOSAL_RNGS_N],
            need_vote_rngs: [[[0;2]; STATUS_VOTE_RNGS_N]; 2],
        };
        packet.height = r.read_u64::<LittleEndian>()?;
        packet.round = r.read_u32::<LittleEndian>()?;
        for chunk_rng in &mut packet.need_proposal_chunk_rngs {
            chunk_rng[0] = r.read_u32::<LittleEndian>()?;
            chunk_rng[1] = r.read_u32::<LittleEndian>()?;
        }
        for is_precommit in 0..2 {
            for vote_rng in &mut packet.need_vote_rngs[is_precommit] {
                vote_rng[0] = r.read_u16::<LittleEndian>()?;
                vote_rng[1] = r.read_u16::<LittleEndian>()?;
            }
        }
        Ok(packet)
    }
}

const PACKET_HEADER_SIZE: usize = 1; // 8 + 8; // 16
struct PacketHeader {
    tag: u8,
    // tag_and_ack: u64,
    // ack_field: u64,
}
impl PacketHeader {
    const fn assert_valid_tag<const TAG: u8>() {
        assert!((TAG & ! PACKET_TYPE_MASK) == 0);
    }

    pub fn new<const TAG: u8>(ack_latest: u64, ack_field: u64) -> PacketHeader {
        Self::assert_valid_tag::<TAG>();
        Self::new_(TAG, ack_latest, ack_field)
    }
    pub fn new_(tag: u8, ack_latest: u64, ack_field: u64) -> PacketHeader {
        PacketHeader {
            tag
            // tag_and_ack: tag as u64 | ((ack_latest) & (u64::MAX >> PACKET_TYPE_BITS) << PACKET_TYPE_BITS),
            // ack_field,
        }
    }

    pub fn write_to(&self, buf: &mut [u8]) -> usize {
        let mut o = 0;
        o += self.tag.write_to(&mut buf[o..]);
        // o += self.tag_and_ack.write_to(&mut buf[o..]);
        // o += self.ack_field  .write_to(&mut buf[o..]);
        o
    }

    pub fn read_from<R: Read>(mut r: R) -> std::io::Result<Self> {
        let tag = r.read_u8()?;
        // let tag_and_ack = r.read_u64::<LittleEndian>()?;
        // let ack_field   = r.read_u64::<LittleEndian>()?;
        Ok(Self {
            tag
            // tag_and_ack,
            // ack_field,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct PubKeySig { roster_i: u16, sig: TMSig, }
impl PubKeySig { const NIL: Self = Self{ roster_i: u16::MAX, sig: TMSig::NIL }; }

// ALT: common consensus packet header: { packet header, height, round, value_id }

// agnostic to prevote/precommit - communicated elsewhere
// NOTE: all votes for the same value_id (or nil)
// #[repr(C)]
#[derive(Debug)]
struct PacketVotes {
    // header
    no_votes_n:  u8,
    yes_votes_n: u8,
    // pad_:     u16, // TODO: useful?
    round:      u32,
    height:     u64,
    value_id:   ValueId,
    // TODO: use u16 roster_idxs instead of pub_keys
    votes:    [PubKeySig; 18],
}
const_assert!(size_of::<PacketVotes>() == 1240); // TODO(azmr): exactly how much space is left
                                                 // after noise/nonce/ECC/...?
                                                 // TODO(phil): figure out the padding here

impl PacketVotes {
    fn write_to(&self, buf: &mut [u8]) -> usize {
        let mut o = 0;
        o += self.no_votes_n .write_to(&mut buf[o..]);
        o += self.yes_votes_n.write_to(&mut buf[o..]);
        o += self.round      .write_to(&mut buf[o..]);
        o += self.height     .write_to(&mut buf[o..]);
        o += self.value_id.0 .write_to(&mut buf[o..]);
        // NOTE(azmr): slight saving of bytes-on-wire if unused? i.e. initial few times each
        for i in 0..(self.no_votes_n + self.yes_votes_n) as usize {
            o += &self.votes[i].roster_i.write_to(&mut buf[o..]);
            o += &self.votes[i].sig   .0.write_to(&mut buf[o..]);
        }
        o
    }

    pub fn read_from<R: Read>(mut r: R) -> std::io::Result<Self> {
        let mut packet = PacketVotes {
            no_votes_n: 0, yes_votes_n: 0, round: 0, height: 0,
            value_id: ValueId::NIL,
            votes: [PubKeySig::NIL; 18],
        };
        packet.no_votes_n  = r.read_u8()?;
        packet.yes_votes_n = r.read_u8()?;
        packet.round       = r.read_u32::<LittleEndian>()?;
        packet.height      = r.read_u64::<LittleEndian>()?;
        r.read_exact(&mut packet.value_id.0)?;
        for i in 0..(packet.no_votes_n + packet.yes_votes_n) as usize {
            packet.votes[i].roster_i = r.read_u16::<LittleEndian>()?;
            r.read_exact(&mut packet.votes[i].sig.0)?;
        }
        Ok(packet)
    }
}

const PROPOSAL_PACKET_EXTRA:    usize = (PACKET_HEADER_SIZE + 56 + 64);
const PROPOSAL_CHUNK_DATA_SIZE: usize = PATH_MTU - PROPOSAL_PACKET_EXTRA;

// NOTE(azmr): this is:
// - conservative in terms of max chunks, value_id, & arrival order
// - assuming a fixed total proposal size
#[derive(Debug)]
struct PacketProposalChunkHeader {
    // header
    chunk_i:       u32,
    proposal_size: u32,
    round:         u32,
    valid_round:   i64, // serialized as u32 with 0xff.ff for -1
    height:        u64,
    proposal_id:   ValueId, // for the total proposal, not just this chunk
    // data:        [u8; 1087], // 1200-113
    // proposer_signature: TMSig,
}
impl PacketProposalChunkHeader {
    const SERIALIZED_SIZE: usize = 4 * 4 + 8 + 32; // 56

    fn write_to(&self, buf: &mut [u8]) -> usize {
        let valid_round: u32 = if self.valid_round >= 0 { self.valid_round.try_into().unwrap() } else { u32::MAX };

        let mut o = 0;
        o        += self.chunk_i      .write_to(&mut buf[o..]);
        o        += self.proposal_size.write_to(&mut buf[o..]);
        o        += self.round        .write_to(&mut buf[o..]);
        o        += valid_round       .write_to(&mut buf[o..]);
        o        += self.height       .write_to(&mut buf[o..]);
        o        += self.proposal_id.0.write_to(&mut buf[o..]);
        // self.data                .write_to(&mut buf[48..]);
        // self.proposer_signature.0.write_to(&mut buf[1135..]);
        o
    }

    pub fn read_from<R: Read>(mut r: R) -> std::io::Result<Self> {
        let mut packet = PacketProposalChunkHeader {
            chunk_i: 0, proposal_size: 0, round: 0, height: 0, valid_round: 0, proposal_id: ValueId::NIL
        };
        packet.chunk_i       = r.read_u32::<LittleEndian>()?;
        packet.proposal_size = r.read_u32::<LittleEndian>()?;
        packet.round         = r.read_u32::<LittleEndian>()?;
        let valid_round      = r.read_u32::<LittleEndian>()?;
        packet.height        = r.read_u64::<LittleEndian>()?;
        r.read_exact(&mut packet.proposal_id.0)?;

        packet.valid_round = if valid_round != u32::MAX { valid_round.into() } else { -1 };
        Ok(packet)
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

#[derive(Clone)]
struct RustIsBadRngWrapper(ChaCha20Rng);
impl snow::types::Random for RustIsBadRngWrapper {
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), snow::Error> {
        self.0.fill(dest);
        Ok(())
    }
}
struct SnowRngResolver {
    pub rng: RustIsBadRngWrapper,
}

impl CryptoResolver for SnowRngResolver {
    fn resolve_rng(&self) -> Option<Box<dyn snow::types::Random>> {
        Some(Box::new(self.rng.clone()))
    }
    fn resolve_dh(&self, choice: &snow::params::DHChoice) -> Option<Box<dyn snow::types::Dh>> {
        snow::resolvers::DefaultResolver::resolve_dh(&snow::resolvers::DefaultResolver, choice)
    }
    fn resolve_hash(&self, choice: &snow::params::HashChoice) -> Option<Box<dyn snow::types::Hash>> {
        snow::resolvers::DefaultResolver::resolve_hash(&snow::resolvers::DefaultResolver, choice)
    }
    fn resolve_cipher(&self, choice: &snow::params::CipherChoice) -> Option<Box<dyn snow::types::Cipher>> {
        snow::resolvers::DefaultResolver::resolve_cipher(&snow::resolvers::DefaultResolver, choice)
    }
}

pub fn run_instances(i: usize) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    let seed: u64 = if i == usize::MAX {
        rand::rng().next_u64()
    } else {
        const MOCK_RNG_SEED_FOR_MULTIPROCESS: u64 = 0xdeadbeef12345;
        MOCK_RNG_SEED_FOR_MULTIPROCESS
    };

    const N: usize = 4;

    let mut crypto_rng = ChaCha20Rng::seed_from_u64(seed);
    let static_private_keys : Vec<_> = (0..N).map(|_| {
        // NOTE: doing this manually to avoid CryptoRng incompatibilities between different rand_core versions
        let mut secret_key = [0u8; 32];
        crypto_rng.fill_bytes(&mut secret_key);
        SigningKey::from(secret_key)
    }).collect();
    let mut cumulative_stake = 0;
    let roster : Vec<SortedRosterMember> = static_private_keys.iter().enumerate().map(|(_, sk)| {
        //let stake = 2000 * (static_private_keys.len() - 1 - i) as u64;
        let stake = 1;
        cumulative_stake += stake;
        SortedRosterMember { pub_key: PubKeyID(sk.verification_key().into()), stake, cumulative_stake }
    }).collect();
    assert!(roster.is_sorted_by(|a,b| a.stake >= b.stake)); // descending

    println!("Roster: {:?}", roster);

    let static_keypair_zero = {
        let kp = snow::Builder::with_resolver("Noise_IK_25519_ChaChaPoly_BLAKE2s".parse().unwrap(), Box::new(SnowRngResolver { rng: RustIsBadRngWrapper(crypto_rng.clone()) })).generate_keypair().unwrap();
        StaticDHKeyPair { private: kp.private.try_into().unwrap(), public: kp.public.try_into().unwrap(), }
    };

    let endpoint_zero : SecureUdpEndpoint = {
        let port : u16 = 3030;
        // let ip = "::1".parse::<std::net::Ipv6Addr>().unwrap();
        let ip = "127.0.0.1".parse::<std::net::Ipv4Addr>().unwrap().to_ipv6_mapped();
        SecureUdpEndpoint { ip_address: ip.octets(), port, public_key: static_keypair_zero.public }
    };

    let evidence_zero = {
        EndpointEvidence { endpoint: endpoint_zero, root_public_key: static_private_keys[0].verification_key().into() }
    };

    if i == usize::MAX {
        // let _joins: [; N];
        for j in 0..N {
            if j == 0 {
                rt.spawn(instance(static_private_keys[j], Some(static_keypair_zero), Some(endpoint_zero), roster.clone(), vec![evidence_zero], None));
            } else {
                rt.spawn(instance(static_private_keys[j], None, None, roster.clone(), vec![evidence_zero], None));
            }
        }
    } else if i == 999 {
        // let _joins: [; N];
        for j in 0..N-1 {
            if j == 0 {
                rt.spawn(instance(static_private_keys[j], Some(static_keypair_zero), Some(endpoint_zero), roster.clone(), vec![evidence_zero], None));
            } else {
                rt.spawn(instance(static_private_keys[j], None, None, roster.clone(), vec![evidence_zero], None));
            }
        }
    } else {
        if i == 0 {
            rt.spawn(instance(static_private_keys[i], Some(static_keypair_zero), Some(endpoint_zero), roster.clone(), vec![evidence_zero], None));
        } else {
            rt.spawn(instance(static_private_keys[i], None, None, roster.clone(), vec![evidence_zero], None));
        }
    }
    rt.block_on(std::future::pending::<()>())
}

#[cfg(test)]
mod tests {
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
        run_instances(usize::MAX);
    }

    #[ignore]
    #[test]
    fn check_proposer_from_height_round() {
        let roster_ = [
            SortedRosterMember{ pub_key: PubKeyID([1;32]), stake: 2000, cumulative_stake: 2000 },
            SortedRosterMember{ pub_key: PubKeyID([2;32]), stake: 1000, cumulative_stake: 3000 },
            SortedRosterMember{ pub_key: PubKeyID([2;32]), stake: 1000, cumulative_stake: 4000 },
            SortedRosterMember{ pub_key: PubKeyID([3;32]), stake: 0000, cumulative_stake: 4000 },
        ];
        let roster = [
            SortedRosterMember{ pub_key: PubKeyID([1;32]), stake: 2, cumulative_stake: 2 },
            SortedRosterMember{ pub_key: PubKeyID([2;32]), stake: 1, cumulative_stake: 3 },
            SortedRosterMember{ pub_key: PubKeyID([2;32]), stake: 1, cumulative_stake: 4 },
            SortedRosterMember{ pub_key: PubKeyID([3;32]), stake: 0, cumulative_stake: 4 },
        ];
        let roster0 = [
            SortedRosterMember{ pub_key: PubKeyID([1;32]), stake: 0, cumulative_stake: 0 },
            SortedRosterMember{ pub_key: PubKeyID([2;32]), stake: 0, cumulative_stake: 0 },
            SortedRosterMember{ pub_key: PubKeyID([3;32]), stake: 0, cumulative_stake: 0 },
        ];
        assert!((None, PubKeyID::NIL) == TMState::proposer_from_height_round(&HashKeys::default(), &[], 2, 1));
        for height in 0..8 {
            for round in 0..6 {
                let (Some(i), _) = TMState::proposer_from_height_round(&HashKeys::default(), &roster_[..], height, round) else { panic!(); };
                println!("BFT Proposer at {}.{}: {}", height, round, i);
                let (Some(i), _) = TMState::proposer_from_height_round(&HashKeys::default(), &roster[..], height, round) else { panic!(); };
                println!("BFT Proposer at {}.{}: {}", height, round, i);
                let (Some(i), _) = TMState::proposer_from_height_round(&HashKeys::default(), &roster[..1], height, round) else { panic!(); };
                println!("BFT Proposer at {}.{}: {}", height, round, i);
                // assert!(TMState::proposer_from_height_round(&roster0, 100, height, round).0.is_none());
            }
        }
        // let (Some(i), _) = TMState::proposer_from_height_round(&roster[..2], 100, heig) else { panic!(); };
        // println!("BFT Proposer at {}.{}: {}", 2, 2, i);
    }

    #[test]
    fn check_nonce_is_ok() {
        assert!(nonce_is_ok(124, 12, !0));
        assert!(!nonce_is_ok(12, 124, !0));
        assert!(nonce_is_ok(120, 124, 0xffff_ffff_ffff_ffef));
    }

    #[test]
    fn check_gen_rngs() {
        struct Test {
            arr: &'static[u8],
            rngs: &'static[[usize; 2]],
        }
        let tests = [
            Test { arr: b"00000000",  rngs: &[[0,8]] },
            Test { arr: b"00010000",  rngs: &[[0,8]] },
            Test { arr: b"10010000",  rngs: &[[1,8]] },
            Test { arr: b"10010001",  rngs: &[[1,7]] },
            Test { arr: b"10011001",  rngs: &[[1,3], [5,7]] },
            Test { arr: b"101101100", rngs: &[[1,2], [4,5], [7,9]] },
            Test { arr: b"101111100", rngs: &[[1,2],        [7,9]] },
        ];

        for (test_i, test) in tests.iter().enumerate() {
            let rngs = gen_mostly_empty_rngs(test.arr.len(), |i| test.arr[i] == b'0');
            assert_eq!(test.rngs, &rngs, "index {}", test_i);
        }
    }
}

