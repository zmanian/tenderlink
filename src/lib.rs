#![allow(dead_code)]
#![allow(unused_parens)]
#![allow(clippy::never_loop)]


use static_assertions::{const_assert};
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

#[derive(PartialEq, Eq, Clone, Copy)]
enum TMStep {
    Propose,
    Prevote,
    // ALT: extra sign step
    Precommit,
}

struct TMDecision {
    value: BlockValue,
    //signatures: Vec<TMSig>, // ability to prove to others e.g. those catching up
}


struct TMVote {
    approve: bool,
    todo_sign_bytes: [u8; 96],
}

#[derive(Clone, Copy, PartialEq)]
struct BlockValue([u8; 6000]);
impl BlockValue {
    fn is_valid(&self) -> TMStatus {
        // TODO
        TMStatus::Pass
    }
}

fn get_bft_value() -> BlockValue {
    // TODO: sim/get from PoW
    BlockValue([0; 6000])
}



#[derive(Copy, Clone, PartialEq, Eq)]
enum TMStatus {
    Indeterminate,
    Pass, // 2f+1 yes
    Fail, // f+1 no
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct ValueId([u8; 32]);
impl ValueId {
    const NIL: Self = Self([0; 32]);
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct PubKeyID([u8; 32]);
impl PubKeyID {
    const NIL: Self = Self([0; 32]);
}
impl std::fmt::Display for PubKeyID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_byte_str(f, &self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct TMSig ([u8; 64]);
impl TMSig {
    const NIL: Self = Self([0; 64]);
}

struct RoundData {
    height: u64,
    round: u32,
    // parallel with sorted roster arrays
    // TODO: keep parallel with each other, but be sparse in members
    proposal: BlockValue,
    proposal_valid_round: i64,
    proposal_sig: TMSig,
    proposal_id: ValueId,
    proposal_checked_validity: TMStatus,

    msg_val_sigs: Vec<[(ValueId, TMSig); 2]>, // prevote then precommit

    anys_n: usize,
    prevotes_n: usize,
    precommits_n: usize,
    valid_prevotes_n: usize,
    valid_precommits_n: usize,
    nil_prevotes_n: usize,
    // TODO: can probably do this from whether *our* node has a valid value
    // TODO: by round or for whole state?
    active_timeout: Option<Timeout>,
    timeout_triggered: [bool; 2],
}
impl RoundData {
    const EMPTY: RoundData = RoundData{
        height: 0,
        round: 0,
        proposal: BlockValue([0; 6000]),
        proposal_valid_round: -1,
        proposal_sig: TMSig([0; 64]),
        proposal_id: ValueId::NIL,
        proposal_checked_validity: TMStatus::Indeterminate,
        // TODO: probably put both step messages next to each other
        msg_val_sigs: Vec::new(),
        valid_prevotes_n: 0,
        valid_precommits_n: 0,
        nil_prevotes_n: 0,
        prevotes_n: 0,
        precommits_n: 0,
        anys_n: 0,

        active_timeout: None,
        timeout_triggered: [false;2],
    };

    // auto-caching
    fn proposal_is_valid(&mut self) -> TMStatus {
        if (self.proposal_checked_validity == TMStatus::Indeterminate &&
            self.proposal_sig != TMSig::NIL) {
            self.proposal_checked_validity = self.proposal.is_valid();
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

fn roster_i_from_pub_key(_pub_key: PubKeyID) -> usize {
    0
}

struct Timeout { time: Instant, height: u64, round: u32, step: TMStep }
impl Timeout {
    fn new(now: Instant, height: u64, round: u32, step: TMStep) -> Timeout {
        use std::time::Duration;
        let timeout = match step {
            TMStep::Propose   => Duration::from_secs(3) + round * Duration::from_millis(500),
            TMStep::Prevote   => Duration::from_secs(3) + round * Duration::from_millis(500),
            TMStep::Precommit => Duration::from_secs(3) + round * Duration::from_millis(500),
        };

        Timeout{ time: now + timeout, height, round, step }
    }
}


struct TMState {
    roster_n: usize,
    my_pub_key: PubKeyID,
    round: u32,
    step: TMStep,
    /// basically the chain of agreed blocks
    decisions: Vec<TMDecision>, // TODO: rearchitect
    /// most recent "possible decision value" - successful proposal + prevote
    /// when valid_value was updated
    valid_value_round: (Option<BlockValue>, i64), // TODO
    /// last value sent for precommit // TODO: non-nil only?
    /// last round on which a *non-nil* value was sent
    locked_value_round: (Option<BlockValue>, i64), // TODO

    // active_proposer_pub_key: [u8; 32],
    // active_proposal_value_round: (Option<BlockValue>, i64),
    /// parallel to roster
    votes: Vec<TMVote>,

    /// treat all processing things as happening at the same time (?)
    timeout_start_height: u64,
    timeout_start_round: u32,
    timeout_step: TMStep,
    next_timeout: Option<(Instant, u64, u32, TMStep)>,

    rounds_data: Vec<RoundData>,
}
impl TMState {
    fn init(my_pub_key: PubKeyID) -> Self {
        Self {
            roster_n: 0,
            my_pub_key,
            round: 0,
            step: TMStep::Propose,
            decisions: Vec::new(), // simple approach: 1 per height
            valid_value_round: (None, -1), // TODO: is this actually protocol-relevant or just a cache?
            locked_value_round: (None, -1),

            // active_proposal_value_round: (None, -1),
            // active_proposer_pub_key: PubKeyID::NIL,
            votes: Vec::new(),

            timeout_start_height: 0,
            timeout_start_round: 0,
            timeout_step: TMStep::Propose,
            next_timeout: None,

            rounds_data: Vec::new(),
        }
    }

    fn height(&self) -> u64 {
        self.decisions.len() as u64
    }


    fn broadcast(&self, step: TMStep, msg: TMMsgData) -> TMStep {
        self.height();
        self.round;
        msg;
        // TODO: sign msg data
        // TODO: can we get away with not signing the step or separately signing the step?
        let _sig = [1; 64];
        // TODO: send to self
        // TODO: send to (some) others
        todo!();
        step
    }

    fn proposer_from_height_round(height: u64, round: u32) -> PubKeyID {
        // TODO: deterministic weighted round robin (hash & mod total zec on cumulative list)
        let mut res = PubKeyID([0; 32]);
        res.0[0] = height as u8;
        res.0[1] = round as u8;
        res
    }

    fn insert_round(&mut self, insert_i: usize, round: u32) -> &mut RoundData {
        self.rounds_data.insert(insert_i, RoundData{
            height: self.height(),
            round,
            msg_val_sigs: vec![[(ValueId::NIL, TMSig::NIL); 2]; self.roster_n],
            ..RoundData::EMPTY
        });
        &mut self.rounds_data[insert_i]
    }

    fn start_round(&mut self, now: Instant, round: u32) {
        self.round = round;
        // self.active_proposal_value_round = (None, -1);

        if Self::proposer_from_height_round(self.height(), round) == self.my_pub_key {
            let proposal = if let Some(valid_value) = self.valid_value_round.0 {
                valid_value
            } else {
                get_bft_value()
            };

            // TODO: simple approach: send proposal messages to self when broadcasting
            // self.active_proposal_value_round = (Some(proposal), self.valid_value_round.1);
            self.step = self.broadcast(TMStep::Propose, TMMsgData::Proposal(proposal, self.valid_value_round.1));
        } else {
            self.step = TMStep::Propose;

            match self.rounds_data.binary_search_by_key(&(self.height(), round), |el| (el.height, el.round)) {
                Ok(round_i)  => &mut self.rounds_data[round_i],
                Err(round_i) => self.insert_round(round_i, round)
            }.active_timeout = Some(Timeout::new(now, self.height(), self.round, TMStep::Propose));
        }
    }

    fn id_from_value(proposal: BlockValue) -> ValueId {
        // TODO: secure hash
        ValueId([proposal.0[0] | 1; 32]) // non-nil
    }

    fn f_from_n(n: u64) -> u64 {
        (n - 1) / 3
    }

    fn check_and_incorporate_msg(&mut self, from_pub_key: PubKeyID, height: u64, round: u32, data: TMMsgData, sig: TMSig) -> TMStatus {
        let is_an_invalid_signature = false; // TODO
        if is_an_invalid_signature { return TMStatus::Fail; }

        let is_signed_by_non_roster_member = false; // TODO (account for roster at round)
        if is_signed_by_non_roster_member { return TMStatus::Fail; }

        // TODO: potentially track < self.height()
        if height != self.height() { return TMStatus::Fail; } // may be valid later if we're catching up

        let roster_i = roster_i_from_pub_key(from_pub_key);

        // TODO: other checks
        // - data size check if we're doing network stuff

        let (is_prev_seen_round, round_i) = match self.rounds_data.binary_search_by_key(&(height, round), |el| (el.height, el.round)) {
            Ok(round_i)  => (true,  round_i),
            Err(round_i) => (false, round_i),
        };

        let status = match data {
            TMMsgData::Proposal(value, _valid_round) => {
                // "is it the correct proposer?"
                let expected_proposer_pub_key = Self::proposer_from_height_round(height, round);
                if from_pub_key != expected_proposer_pub_key {
                    eprintln!("BFT at {}.{}: received proposal from non-proposer expected {} ({}), received from {}. Ignoring latest...", height, round, roster_i, expected_proposer_pub_key, from_pub_key);
                    return TMStatus::Fail;
                }

                // "have they previously proposed a different value?"
                if (is_prev_seen_round &&
                    self.rounds_data[round_i].proposal_sig != TMSig::NIL &&
                    self.rounds_data[round_i].proposal_id  != Self::id_from_value(value))
                {
                    eprintln!("BFT at {}.{}: proposer {} proposed 2 different values. Ignoring latest...", height, round, roster_i);
                    return TMStatus::Fail;
                }

                TMStatus::Pass
            }

            TMMsgData::Prevote(v_id) | TMMsgData::Precommit(v_id) => {
                // TODO: check if this person has previously voted differently

                if ! is_prev_seen_round && self.rounds_data[round_i].proposal_sig == TMSig::NIL {
                    // if we don't have a real proposal yet we can't check for
                    TMStatus::Indeterminate
                } else if self.rounds_data[round_i].proposal_id != v_id {
                    eprintln!("BFT at {}.{}: finalizer {} voted on 2 different values. Ignoring latest...", height, round, roster_i);
                    return TMStatus::Fail;
                } else {
                    TMStatus::Pass
                }
            }
        };

        // TODO: more checks?

        // Preliminary checks now finished (although not infallible from here) //////////////////////////

        if ! is_prev_seen_round {
            self.insert_round(round_i, round);
        }
        let round_data = &mut self.rounds_data[round_i];

        // TODO: amend knowledge of rounds & update metadata
            // TODO(code): collapse

        match data {
            TMMsgData::Proposal(value, valid_round) => {
                // TODO: check expected proposer here if not above

                if is_prev_seen_round { // element already in vector @ `round_i`
                    let prev_value     = round_data.proposal;
                    let prev_value_sig = round_data.proposal_sig;

                    if prev_value_sig == TMSig::NIL { // votes but value not seen before
                    } else if prev_value != value { // TODO: id
                        eprintln!("BFT ERROR at {}.{}: proposer {} signed 2 different values. Ignoring latest...", height, round, roster_i);
                        return TMStatus::Fail;
                    } else {
                        return TMStatus::Pass; // already good
                    }
                }

                round_data.proposal             = value;
                round_data.proposal_valid_round = valid_round;
                round_data.proposal_sig         = sig;
                round_data.proposal_id          = Self::id_from_value(value);

                // TODO: include signed prevote & precommit for self?
            }

            TMMsgData::Prevote(v_id) | TMMsgData::Precommit(v_id) => {
                let is_precommit = if let TMMsgData::Precommit(..) = data { 1 } else { 0 };

                // TODO: check height

                // Add the signature to the list & update counts
                let new = &mut round_data.msg_val_sigs[roster_i];
                let old = *new;
                new[is_precommit] = (v_id, sig);


                let old_has_sigs     = [(old[0].1 != TMSig::NIL) as usize, (old[1].1 != TMSig::NIL) as usize];
                let new_has_sigs     = [(new[0].1 != TMSig::NIL) as usize, (new[1].1 != TMSig::NIL) as usize];
                let old_has_any_sigs = old_has_sigs[0] | old_has_sigs[1];
                let new_has_any_sigs = new_has_sigs[0] | new_has_sigs[1];

                if old_has_sigs[is_precommit] != 0 && old[is_precommit] != new[is_precommit] {
                    eprintln!("BFT ERROR at {}.{}: finalizer {} voted on 2 different values. Ignoring latest...", height, round, roster_i);
                    return TMStatus::Fail;
                }

                let mut old_status = [[0,0], [0,0]];
                old_status[0][(old[0].0 != ValueId::NIL) as usize] = 1;
                old_status[1][(old[1].0 != ValueId::NIL) as usize] = 1;
                let mut new_status = [[0,0], [0,0]];
                new_status[0][(new[0].0 != ValueId::NIL) as usize] = 1;
                new_status[1][(new[1].0 != ValueId::NIL) as usize] = 1;

                // add 1 to counts that have been updated by this message
                round_data.anys_n             += new_has_any_sigs - old_has_any_sigs;
                round_data.prevotes_n         += new_has_sigs[0]  - old_has_sigs[0];
                round_data.precommits_n       += new_has_sigs[1]  - old_has_sigs[1];
                round_data.valid_prevotes_n   += new_status[0][1] as usize - old_status[0][1] as usize;
                round_data.valid_precommits_n += new_status[1][1] as usize - old_status[1][1] as usize;
                round_data.nil_prevotes_n     += new_status[0][0] as usize - old_status[0][0] as usize;
            }
        }

        status
    }

    fn prune_unnecessary_data(&mut self) {
        // TODO (perf): drop 2f+1 nil-voted rounds before n-2
        todo!();
    }


    fn bft_update(&mut self) {
        let now = Instant::now();
        let f = Self::f_from_n(self.roster_n as u64) as usize;

        for i in 0..self.rounds_data.len() {
            // TODO: don't spam "while" messages repeatedly
            let is_current_height_and_round = (self.height(), self.round) == (self.rounds_data[i].height, self.rounds_data[i].round);

            // line 11: init proposal period
            // (done elsewhere)

            // line 22: receive first proposal this height: prevote
            // > upon <PROPOSAL, h_p, round_p, v, −1> from proposer(h_p, round_p)
            // > while step_p = propose do
            // TODO: merge conditionals with below, they massively overlap
            if (is_current_height_and_round &&
                self.rounds_data[i].proposal_sig != TMSig::NIL && // we have received the proposal value
                self.rounds_data[i].proposal_valid_round != -1 &&
                self.step == TMStep::Propose)
            {
                // TODO: do we want to prevote NIL on currently-indeterminate?
                // ALT: send NIL then later override with time-tagged message
                if self.rounds_data[i].proposal_is_valid() == TMStatus::Pass && (
                    self.locked_value_round.1 == -1 ||
                    self.locked_value_round.0 == Some(self.rounds_data[i].proposal)) // TODO(perf): use (previously-checked) ids for easier comparison?
                {
                    self.step = self.broadcast(TMStep::Prevote, TMMsgData::Prevote(self.rounds_data[i].proposal_id));
                } else {
                    self.step = self.broadcast(TMStep::Prevote, TMMsgData::Prevote(ValueId::NIL));
                }
            }

            // line 28: received 2f+1 prevotes: prevote
            // > upon <PROPOSAL, h_p, round_p, v, vr> from proposer(h_p, round_p) AND 2f+1 <PREVOTE, h_p, vr, id(v)>
            // > while step_p = propose && (0 <= vr && vr < round_p)
            if (is_current_height_and_round &&
                self.rounds_data[i].proposal_sig != TMSig::NIL &&
                2*f+1 <= self.rounds_data[i].valid_prevotes_n &&
                self.step == TMStep::Propose &&
                0 <= self.rounds_data[i].proposal_valid_round && self.rounds_data[i].proposal_valid_round < self.round as i64) // we have received the proposal value
            {
                if self.rounds_data[i].proposal_is_valid() == TMStatus::Pass && (
                    self.locked_value_round.1 <= self.rounds_data[i].proposal_valid_round ||
                    self.locked_value_round.0 == Some(self.rounds_data[i].proposal))
                {
                    self.step = self.broadcast(TMStep::Prevote, TMMsgData::Prevote(self.rounds_data[i].proposal_id));
                } else {
                    self.step = self.broadcast(TMStep::Prevote, TMMsgData::Prevote(ValueId::NIL));
                }
            }

            // line 34: last orders on prevote period
            // > upon 2f+1 <PREVOTE, h_p, round_p, ∗> while step_p = prevote for the first time do
            if (is_current_height_and_round &&
                // don't need the proposal itself
                2*f+1 <= self.rounds_data[i].prevotes_n &&
                self.step == TMStep::Prevote &&
                !self.rounds_data[i].timeout_triggered[0]) // "for the first time" // ALT: round.timeout_step != TMStep::Prevote
            {
                self.rounds_data[i].timeout_triggered[0] = true;
                self.rounds_data[i].active_timeout = Some(Timeout::new(now, self.height(), self.round, TMStep::Prevote));
            }

            // line 36: seen 2f+1 valid prevotes: lock, valid, precommit
            // > upon <PROPOSAL, h_p, round_p, v, ∗> from proposer(h_p, round_p) AND 2f+1 <PREVOTE, h_p, round_p, id(v)>
            // > while valid(v) && step_p >= prevote for the first time do
            if (is_current_height_and_round &&
                self.rounds_data[i].proposal_sig != TMSig::NIL &&
                2*f+1 <= self.rounds_data[i].valid_prevotes_n &&
                self.rounds_data[i].proposal_is_valid() == TMStatus::Pass &&
                (self.step == TMStep::Prevote || self.step == TMStep::Precommit)) // TODO: "for the first time"
            {
                if self.step == TMStep::Prevote {
                    self.locked_value_round = (Some(self.rounds_data[i].proposal), self.round as i64);
                    self.step = self.broadcast(TMStep::Precommit, TMMsgData::Precommit(self.rounds_data[i].proposal_id));
                }
                self.valid_value_round = (Some(self.rounds_data[i].proposal), self.round as i64);
            }

            // line 44: seen 2f+1 nil prevotes: precommit nil
            // > upon 2f+1 <PREVOTE, h_p, round_p, nil>
            // > while step_p = prevote do
            if (is_current_height_and_round &&
                2*f+1 <= self.rounds_data[i].nil_prevotes_n &&
                self.step == TMStep::Prevote)
            {
                self.step = self.broadcast(TMStep::Precommit, TMMsgData::Precommit(ValueId::NIL));
            }

            // line 47: last orders on precommit period
            // > upon 2f+1 <PRECOMMIT, h_p, round_p, ∗> for the first time do
            if (is_current_height_and_round &&
                2*f+1 <= self.rounds_data[i].precommits_n &&
                !self.rounds_data[i].timeout_triggered[1])
            {
                self.rounds_data[i].timeout_triggered[1] = true;
                self.rounds_data[i].active_timeout = Some(Timeout::new(now, self.height(), self.round, TMStep::Precommit));
            }

            // line 49: value decided
            // > upon <PROPOSAL, h_p, r, v, ∗> from proposer(h_p, r) AND 2f+1 <PRECOMMIT, h_p, r, id(v)>
            // > while decision_p[h_p] = nil do
            if (self.height() == self.rounds_data[i].height && // any round
                self.rounds_data[i].proposal_sig != TMSig::NIL &&
                2*f+1 <= self.rounds_data[i].precommits_n &&
                self.rounds_data[i].proposal_is_valid() == TMStatus::Pass)
            {
                self.decisions.push(TMDecision {
                    value: self.rounds_data[i].proposal,
                    // value_sig: self.rounds_data[i].proposal_sig,
                    // votes: self.rounds_data[i].msg_val_sigs
                });
            }

            // line 55: round catchup
            // > upon f+1 <∗, h_p, round, ∗, ∗> with round > round_p do
            if (self.height() == self.rounds_data[i].height &&
                self.round    <  self.rounds_data[i].round  &&
                f+1 <= self.rounds_data[i].anys_n)
            {
                self.start_round(now, self.rounds_data[i].round)
            }

            // timeouts
            if let Some(timeout) = &self.rounds_data[i].active_timeout &&
                timeout.time <= now &&
                self.height() == timeout.height &&
                self.round    == timeout.round
            {
                // TODO(code): can we just use *our* step or is there a possible sequence issue? (from the presence of step checks, probably not)
                match timeout.step {
                    TMStep::Propose => if self.step == TMStep::Propose {
                        self.step = self.broadcast(TMStep::Prevote, TMMsgData::Prevote(ValueId::NIL));
                    },
                    TMStep::Prevote => if self.step == TMStep::Prevote {
                        self.step = self.broadcast(TMStep::Precommit, TMMsgData::Precommit(ValueId::NIL));
                    },
                    TMStep::Precommit => self.start_round(now, self.round + 1),
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

#[derive(Clone, Copy)]
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

fn fmt_byte_str(f: &mut std::fmt::Formatter<'_>, bytes: &[u8]) -> std::fmt::Result {
    for b in bytes { write!(f, "{:02x}", b)?; }
    Ok(())
}

fn fmt_prefixed_byte_str(f: &mut std::fmt::Formatter<'_>, pre: &str, bytes: &[u8]) -> std::fmt::Result {
    write!(f, "{}", pre)?;
    for b in bytes { write!(f, "{:02x}", b)?; }
    Ok(())
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

fn nonce_is_ok(nonce: u64, nonce_ack_latest: u64, nonce_ack_field: u64) -> bool {
    let mut ok = true;
    if nonce > nonce_ack_latest && nonce > nonce_ack_latest + NONCE_FORWARD_JUMP_TOLERANCE { ok = false; }
    if nonce == nonce_ack_latest { ok = false; }
    if nonce + 64 < nonce_ack_latest { ok = false; }
    if nonce < nonce_ack_latest && 1_u64 << (nonce_ack_latest - nonce) & nonce_ack_field != 0 { ok = false; }
    ok
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

async fn instance(my_root_private_key: SigningKey, my_static_keypair: Option<StaticDHKeyPair>, my_endpoint: Option<SecureUdpEndpoint>, roster: Vec<[u8; 32]>, mut roster_endpoint_evidence: Vec<EndpointEvidence>, maybe_seed: Option<u128>) -> std::io::Result<()> {
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

    let sock = tokio::net::UdpSocket::bind(SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::UNSPECIFIED, my_endpoint.map(|e|e.port).unwrap_or(0), 0, 0))).await.unwrap();
    let my_port = sock.local_addr().unwrap().port();

    let mut peers : Vec<Peer> = roster.iter().filter(|k| **k != my_root_public_key.as_ref()).map(|k| Peer {
        root_public_key: *k,
        ..Peer::default()
    }).collect();

    for evidence in &roster_endpoint_evidence {
        if let Some(i) = peers.iter().position(|p| p.root_public_key == evidence.root_public_key) {
            peers[i].endpoint = Some(evidence.endpoint);
        }
    }
    println!("socket port={:05}, peers endpoints={:?}", my_port, peers.iter().map(|p|p.endpoint).collect::<Vec<_>>());

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

                    if let Some(peer_endpoint) = peer.endpoint {
                        if let Some(transport) = &mut peer.transport_state {
                            if peer.connection_is_unknown {
                                // Gossip evidence in order to trigger upgrade
                                if let Some(evidence) = my_endpoint_evidence {
                                    let mut c = Cursor::new(&mut send_buf1[..]);
                                    c.write_all(&[PACKET_TAG_ENDPOINT_EVIDENCE]).unwrap();
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
                                let length = transport.write_message(peer.on_send_next_nonce, &[PACKET_TAG_HEARTBEAT], &mut send_buf2[8..]).unwrap();
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
                            let mut outgoing_state = snow::Builder::new(noise_params.clone())
                                .local_private_key(&my_static_keypair.private).unwrap()
                                .remote_public_key(&peer_endpoint.public_key).unwrap()
                                .build_initiator().unwrap();
                            let length = outgoing_state.write_message(&[PACKET_TAG_CLIENT_HELLO], &mut send_buf2).unwrap();
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
                                c.write_all(&[PACKET_TAG_ENDPOINT_EVIDENCE]).unwrap();
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
                        fn finish_outgoing_handshake(buf: &mut [u8], sock: &tokio::net::UdpSocket, peer_endpoint: SecureUdpEndpoint, peer: &mut Peer, transport: StatelessTransportState, nonce: u64, connection_is_unknown: bool) {
                            let start_nonce = rand::random::<u64>() >> 1;
                            let tag         = if connection_is_unknown { PACKET_TAG_CLIENT_UNKNOWN_ACK } else { PACKET_TAG_CLIENT_ACK };
                            let length      = transport.write_message(start_nonce, &[tag], &mut buf[8..]).unwrap();
                            buf[0..8].copy_from_slice(&start_nonce.to_le_bytes());
                            match sock.try_send_to(&buf[0..8+length], SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer_endpoint.ip_address), peer_endpoint.port, 0, 0))) {
                                Ok(_) => (),
                                Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                                Err(error) => println!("Socket error: {:?}", error),
                            }

                            peer.transport_state                    = Some(transport);
                            peer.outgoing_handshake_state           = None;
                            peer.pending_client_ack_transport_state = None;
                            peer.nonce_ack_latest                   = nonce;
                            peer.nonce_ack_field                    = !0;
                            peer.connection_is_unknown              = connection_is_unknown;
                            peer.on_send_next_nonce                 = start_nonce + 1;
                        }

                        if length >= 8 {
                            nonce = u64::from_le_bytes(recv_buf2[0..8].try_into().unwrap());
                            if length == 8 { break; } // presumably we don't care about standalone nonces
                            let local_msg = &recv_buf2[8..length];
                            if local_msg == [PACKET_TAG_SERVER_HELLO] {
                                // TODO hash
                                if peer.pending_client_ack_transport_state.is_none() || my_port > peer_endpoint.port {
                                    if let Ok(transport) = peer.outgoing_handshake_state.take().unwrap().into_stateless_transport_mode() {
                                        println!("{:05}: Finished outgoing handshake and got nonce {} with {}", my_port, nonce, addr);
                                        finish_outgoing_handshake(&mut send_buf2, &sock, peer_endpoint, peer, transport, nonce, false);
                                    }
                                    break;
                                }
                            } else if local_msg.len() == 1 + 18 && local_msg[0] == PACKET_TAG_SERVER_UNKNOWN_HELLO {
                                let other_side_ip       = &local_msg[1..1+16];
                                let other_side_port     = &local_msg[1+16..1+18];
                                let other_side_endpoint = SecureUdpEndpoint { ip_address: other_side_ip.try_into().unwrap(), port: u16::from_le_bytes(other_side_port.try_into().unwrap()), public_key: my_static_keypair.public };
                                // TODO hash
                                if let Ok(transport) = peer.outgoing_handshake_state.take().unwrap().into_stateless_transport_mode() {
                                    println!("{:05}: Finished outgoing unknown handshake and got nonce {} with {}, I am percieved as {:?}", my_port, nonce, addr, other_side_endpoint);

                                    if my_endpoint_evidence.is_none() {
                                        let evidence = EndpointEvidence { endpoint: other_side_endpoint, root_public_key: my_root_public_key.into() };
                                        println!("{:05}: I am locking in the endpoint evidence {:?}", my_port, evidence);
                                        my_endpoint_evidence = Some(evidence);
                                    }

                                    finish_outgoing_handshake(&mut send_buf2, &sock, peer_endpoint, peer, transport, nonce, true);
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
                        if local_msg == &[PACKET_TAG_CLIENT_ACK] {
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
                let mut incoming_state = snow::Builder::new(noise_params.clone())
                    .local_private_key(&my_static_keypair.private).unwrap()
                    .build_responder().unwrap();
                if let Ok(length) = incoming_state.read_message(raw_msg, &mut recv_buf2) {
                    let local_msg = &recv_buf2[0..length];
                    if local_msg == &[PACKET_TAG_CLIENT_HELLO] {
                        let client_endpoint = SecureUdpEndpoint { public_key: incoming_state.get_remote_static().unwrap().try_into().unwrap(), ip_address: from_ip, port: from_port };
                        println!("{:05}: Server recieved client hello from static key = {:?}", my_port, client_endpoint);
                        // TODO hash
                        if peer.outgoing_handshake_state.is_none() || my_port <= peer_endpoint.port {
                            let hello_bytes = &[PACKET_TAG_SERVER_HELLO];
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
                            if local_msg == [PACKET_TAG_CLIENT_UNKNOWN_ACK] {
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
                let mut incoming_state = snow::Builder::new(noise_params.clone())
                    .local_private_key(&my_static_keypair.private).unwrap()
                    .build_responder().unwrap();
                if let Ok(length) = incoming_state.read_message(raw_msg, &mut recv_buf2) {
                    let local_msg = &recv_buf2[0..length];
                    if local_msg == [PACKET_TAG_CLIENT_HELLO] {
                        let client_endpoint = SecureUdpEndpoint { public_key: incoming_state.get_remote_static().unwrap().try_into().unwrap(), ip_address: from_ip, port: from_port };
                        println!("{:05}: Server recieved client hello from unknown peer with static key = {:?}", my_port, client_endpoint);

                        let start_nonce = rand::random::<u64>() >> 1;
                        send_buf1[0..8].copy_from_slice(&u64::to_le_bytes(start_nonce));
                        send_buf1[8] = PACKET_TAG_SERVER_UNKNOWN_HELLO;
                        send_buf1[8+1..8+1+16].copy_from_slice(&from_ip);
                        send_buf1[8+1+16..8+1+16+2].copy_from_slice(&from_port.to_le_bytes());
                        let length = incoming_state.write_message(&send_buf1[0..8+1+16+2], &mut send_buf2).unwrap();
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
        let msg: &[u8] = msg.unwrap();
        if msg.len() == 0 { continue; }
        let tag = msg[0];

        if peer_is_unknown {
            let peer = &mut unknown_peers[peer_index];
            peer.watch_dog = Instant::now();
            nonce_update(nonce, &mut peer.nonce_ack_latest, &mut peer.nonce_ack_field);

            match tag {
                PACKET_TAG_ENDPOINT_EVIDENCE => match EndpointEvidence::read_from(&msg[1..]) {
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

            match tag {
                PACKET_TAG_HEARTBEAT => if peer.connection_is_unknown {
                    println!("{:05}: Got a heartbeat, this means that the other side does not consider me unknown anymore!", my_port);
                    peer.connection_is_unknown = false;
                    continue;
                }

                PACKET_TAG_ENDPOINT_EVIDENCE => match EndpointEvidence::read_from(&msg[1..]) {
                    Ok(evidence) => if let Some(i) = peers.iter().position(|p| p.root_public_key == evidence.root_public_key) {
                        peers[i].endpoint = Some(evidence.endpoint);
                        roster_endpoint_evidence.retain(|e| e.root_public_key != evidence.root_public_key);
                        roster_endpoint_evidence.push(evidence);
                    }
                    Err(err) => eprintln!("{:05}: couldn't read endpoint evidence: {}", my_port, err),
                }

                _ => {} // println!("{}:  From known peer!   field={:016X} Got '{:?}' from {}", my_port, peer.nonce_ack_field, msg, addr);
            }
            continue;
        }
    }
}

// network
const PACKET_TAG_CLIENT_HELLO         : u8 = 0;
const PACKET_TAG_CLIENT_UNKNOWN_ACK   : u8 = 1;
const PACKET_TAG_CLIENT_ACK           : u8 = 2;
const PACKET_TAG_SERVER_UNKNOWN_HELLO : u8 = 3;
const PACKET_TAG_SERVER_HELLO         : u8 = 4;
const PACKET_TAG_HEARTBEAT            : u8 = 5;
const PACKET_TAG_ENDPOINT_EVIDENCE    : u8 = 6;
// consensus
const PACKET_TAG_PREVOTE_SIGNATURES   : u8 = 7;
const PACKET_TAG_PRECOMMIT_SIGNATURES : u8 = 8;
const PACKET_TAG_COUNT                : u8 = 9;

const PACKET_TAG_NAMES: [&str; PACKET_TAG_COUNT as usize] = {
    let mut names = ["<MISSING>"; PACKET_TAG_COUNT as usize];
    names[PACKET_TAG_CLIENT_HELLO         as usize] = "CLIENT_HELLO";
    names[PACKET_TAG_CLIENT_UNKNOWN_ACK   as usize] = "CLIENT_UNKNOWN_ACK";
    names[PACKET_TAG_CLIENT_ACK           as usize] = "CLIENT_ACK";
    names[PACKET_TAG_SERVER_UNKNOWN_HELLO as usize] = "SERVER_UNKNOWN_HELLO";
    names[PACKET_TAG_SERVER_HELLO         as usize] = "SERVER_HELLO";
    names[PACKET_TAG_HEARTBEAT            as usize] = "HEARTBEAT";
    names[PACKET_TAG_ENDPOINT_EVIDENCE    as usize] = "ENDPOINT_EVIDENCE";
    names[PACKET_TAG_PREVOTE_SIGNATURES   as usize] = "PREVOTE_SIGNATURES";
    names[PACKET_TAG_PRECOMMIT_SIGNATURES as usize] = "PRECOMMIT_SIGNATURES";
    const_assert!(PACKET_TAG_COUNT == 9); // keep names array updated when adding other tags
    names
};
fn packet_name_from_tag(tag: u8) -> &'static str { PACKET_TAG_NAMES.get(tag as usize).unwrap_or(&"<UNKNOWN>") }

// NOTE(azmr): could add packet sizes so we can check all sizes in 1 location

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
