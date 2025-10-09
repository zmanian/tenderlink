#![allow(dead_code)]
#![allow(unused_parens)]
#![allow(clippy::never_loop)]


use static_assertions::{const_assert};
use std::{io::{Read, Write}, net::{Ipv6Addr, SocketAddr, SocketAddrV6}, time::Duration};
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

#[derive(Clone)]
struct SortedRosterMember {
    pub_key: PubKeyID,
    stake: u64,
    cumulative_stake: u64, // everyone in array prior to this point (used for determining proposer)
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
impl ValueId { const NIL: Self = Self([0; 32]); }
impl std::fmt::Display for ValueId { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { fmt_byte_str(f, &self.0) } }

#[derive(Clone, Copy, PartialEq, Eq)]
struct PubKeyID([u8; 32]);
impl PubKeyID { const NIL: Self = Self([0; 32]); }
impl std::fmt::Display for PubKeyID { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { fmt_byte_str(f, &self.0) } }

#[derive(Clone, Copy, PartialEq, Eq)]
struct TMSig ([u8; 64]);
impl TMSig { const NIL: Self = Self([0; 64]); }

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

    rounds_data: Vec<RoundData>,
}
impl TMState {
    fn init(my_pub_key: PubKeyID) -> Self {
        Self {
            roster_n: 0, // TODO: get from elsewhere
            my_pub_key,
            round: 0,
            step: TMStep::Propose,
            decisions: Vec::new(), // simple approach: 1 per height
            valid_value_round: (None, -1), // TODO: is this actually protocol-relevant or just a cache?
            locked_value_round: (None, -1),

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

    const ROSTER_MAX_N: usize = 100;
    /// Deterministic weighted round robin (hash & mod total zec on cumulative list)
    fn proposer_from_height_round(roster: &[SortedRosterMember], roster_max_n: usize, height: u64, round: u32) -> (Option<usize>, PubKeyID) {
        if roster.len() == 0 {
            eprintln!("BFT ERROR: trying to get proposer from empty roster");
            return (None, PubKeyID::NIL); // TODO: is a fixed value here exploitable? Presumably nobody can sign for it?
        }

        // NOTE(azmr): this 32-byte crypto-hashing is almost certainly overkill!
        let key: [u8; 32] = blake3::Hasher::new_derive_key("BFT Proposer").finalize().into();
        let hash = blake3::Hasher::new_keyed(&key).update(&u64::to_le_bytes(height)).update(&u32::to_le_bytes(round)).finalize();

        let mut hash_stake_bytes = [0; 8];
        hash.as_bytes()[..8].write_to(&mut hash_stake_bytes);
        let hash_stake = u64::from_le_bytes(hash_stake_bytes);

        let last_included_i = usize::min(roster_max_n, roster.len()) - 1;
        let total_included_stake = roster[last_included_i].cumulative_stake;
        if total_included_stake == 0 {
            eprintln!("BFT ERROR: all roster members have no stake");
            return (None, PubKeyID::NIL); // TODO: is a fixed value here exploitable? Presumably nobody can sign for it?
        }


        let proposer_stake = hash_stake % total_included_stake;

        let roster_i = roster.partition_point(|m| m.cumulative_stake <= proposer_stake);
        println!("proposer stake hash: {} ==u64=> {:016x} ==%{}=> {} ==i=> {}", hash, hash_stake, total_included_stake, proposer_stake, roster_i);
        (Some(roster_i), roster[roster_i].pub_key)
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

    fn start_round(&mut self, roster: &[SortedRosterMember], now: Instant, round: u32) {
        self.round = round;
        // self.active_proposal_value_round = (None, -1);

        if Self::proposer_from_height_round(roster, Self::ROSTER_MAX_N, self.height(), round).1 == self.my_pub_key {
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
        let key: [u8; 32] = blake3::Hasher::new_derive_key("BFT Value ID").finalize().into();
        ValueId(*blake3::keyed_hash(&key, &proposal.0).as_bytes())
    }

    fn f_from_n(n: u64) -> u64 {
        (n - 1) / 3
    }

    fn check_and_incorporate_msg(&mut self, roster: &[SortedRosterMember], from_pub_key: PubKeyID, height: u64, round: u32, data: TMMsgData, sig: TMSig) -> TMStatus {
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
                let (_, expected_proposer_pub_key) = Self::proposer_from_height_round(roster, Self::ROSTER_MAX_N, height, round);
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


    fn bft_update(&mut self, roster: &[SortedRosterMember]) {
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
                self.start_round(roster, now, self.rounds_data[i].round)
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
                    TMStep::Precommit => self.start_round(roster, now, self.round + 1),
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

// NOTE: buf can be open-ended
trait SliceWrite         { fn write_to(&self, buf: &mut [u8]) -> usize; }
impl SliceWrite for u64  { fn write_to(&self, buf: &mut [u8]) -> usize { buf[0..8].copy_from_slice(&u64::to_le_bytes(*self)); 8 } }
impl SliceWrite for u32  { fn write_to(&self, buf: &mut [u8]) -> usize { buf[0..4].copy_from_slice(&u32::to_le_bytes(*self)); 4 } }
impl SliceWrite for u16  { fn write_to(&self, buf: &mut [u8]) -> usize { buf[0..2].copy_from_slice(&u16::to_le_bytes(*self)); 2 } }
impl SliceWrite for u8   { fn write_to(&self, buf: &mut [u8]) -> usize { buf[0] = *self;                                       1 } }
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
    pub fn write_to(&self, buf: &mut [u8]) -> usize {
        let o = self.endpoint.write_to(&mut buf[..]);
        o + self.root_public_key.write_to(&mut buf[o..])
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

// returns true if a is initiator
fn contended_noise_is_initiator(a: &[u8; 32], b: &[u8; 32]) -> bool {
    // TODO: do we want a fast insecure hash for this kind of thing?
    // TODO: talk to Zooko about not paying the upfront key derive cost every time
    let key: [u8; 32] = blake3::Hasher::new_derive_key("BFT Connect Contention").finalize().into(); // NOTE(azmr): skipping update
    let a_to_b_hash = blake3::Hasher::new_keyed(&key).update(a).update(b).finalize();
    let b_to_a_hash = blake3::Hasher::new_keyed(&key).update(b).update(a).finalize();
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

async fn instance(my_root_private_key: SigningKey, my_static_keypair: Option<StaticDHKeyPair>, my_endpoint: Option<SecureUdpEndpoint>, roster: Vec<SortedRosterMember>, mut roster_endpoint_evidence: Vec<EndpointEvidence>, maybe_seed: Option<u128>) -> std::io::Result<()> {
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

    let mut peers : Vec<Peer> = roster.iter().filter(|m| m.pub_key.0 != my_root_public_key.as_ref())
        .map(|m| Peer { root_public_key: m.pub_key.0, ..Peer::default() }).collect();

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
        fn send_sock_msg(sock: &tokio::net::UdpSocket, peer_endpoint: SecureUdpEndpoint, msg: &[u8]) {
            match sock.try_send_to(msg, SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::from(peer_endpoint.ip_address), peer_endpoint.port, 0, 0))) {
                Ok(_) => (),
                Err(ref e) if e.kind() == tokio::io::ErrorKind::WouldBlock => (), // not writable, drop
                Err(error) => println!("Socket error: {:?}", error),
            }
        }
        fn send_noise_msg(transport: &mut StatelessTransportState, sock: &tokio::net::UdpSocket, peer_endpoint: SecureUdpEndpoint, on_send_next_nonce: &mut u64, send_buf2: &mut [u8], msg: &[u8]) {
            on_send_next_nonce.write_to(&mut send_buf2[0..8]);
            let length = transport.write_message(*on_send_next_nonce, msg, &mut send_buf2[8..]).unwrap();
            *on_send_next_nonce += 1;
            send_sock_msg(sock, peer_endpoint, &send_buf2[0..8+length]);
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

                    if let Some(peer_endpoint) = peer.endpoint {
                        if let Some(transport) = &mut peer.transport_state {
                            if peer.connection_is_unknown {
                                // Gossip evidence in order to trigger upgrade
                                if let Some(evidence) = my_endpoint_evidence {
                                    send_buf1[0] = PACKET_TAG_ENDPOINT_EVIDENCE;
                                    let len1 = 1 + evidence.write_to(&mut send_buf1[1..]);
                                    send_noise_msg(transport, &sock, peer_endpoint, &mut peer.on_send_next_nonce, &mut send_buf2, &send_buf1[..len1]);
                                }
                            }
                            else {
                                send_noise_msg(transport, &sock, peer_endpoint, &mut peer.on_send_next_nonce, &mut send_buf2, &[PACKET_TAG_HEARTBEAT]);
                            }
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
                            let length = outgoing_state.write_message(&[PACKET_TAG_CLIENT_HELLO], &mut send_buf2).unwrap();
                            // TODO: no nonce?
                            send_sock_msg(&sock, peer_endpoint, &send_buf2[0..length]);
                            peer.outgoing_handshake_state = Some(outgoing_state);
                        }

                        if let Some(transport) = &mut peer.transport_state {
                            if let Some(evidence) = roster_endpoint_evidence.choose(&mut base_rng) {
                                send_buf1[0] = PACKET_TAG_ENDPOINT_EVIDENCE;
                                let len1     = 1 + evidence.write_to(&mut send_buf1[1..]);
                                send_noise_msg(transport, &sock, peer_endpoint, &mut peer.on_send_next_nonce, &mut send_buf2, &send_buf1[..len1]);
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
                        fn finish_outgoing_handshake(send_buf2: &mut [u8], sock: &tokio::net::UdpSocket, peer_endpoint: SecureUdpEndpoint, peer: &mut Peer, mut transport: StatelessTransportState, nonce: u64, connection_is_unknown: bool) {
                            let tag = if connection_is_unknown { PACKET_TAG_CLIENT_UNKNOWN_ACK } else { PACKET_TAG_CLIENT_ACK };
                            peer.on_send_next_nonce = rand::random::<u64>() >> 1;
                            send_noise_msg(&mut transport, sock, peer_endpoint, &mut peer.on_send_next_nonce, send_buf2, &[tag]);

                            peer.transport_state                    = Some(transport);
                            peer.outgoing_handshake_state           = None;
                            peer.pending_client_ack_transport_state = None;
                            peer.nonce_ack_latest                   = nonce;
                            peer.nonce_ack_field                    = !0;
                            peer.connection_is_unknown              = connection_is_unknown;
                        }

                        if length >= 8 {
                            nonce = u64::from_le_bytes(recv_buf2[0..8].try_into().unwrap());
                            if length == 8 { break; } // presumably we don't care about standalone nonces
                            let local_msg = &recv_buf2[8..length];
                            if local_msg == [PACKET_TAG_SERVER_HELLO] {
                                if peer.pending_client_ack_transport_state.is_none() || !contended_noise_is_initiator(&my_root_public_key.into(), &peer.root_public_key) {
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
                        if local_msg == [PACKET_TAG_CLIENT_ACK] {
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
                    let local_msg = &recv_buf2[0..length];
                    if local_msg == &[PACKET_TAG_CLIENT_HELLO] {
                        let client_endpoint = SecureUdpEndpoint { public_key: incoming_state.get_remote_static().unwrap().try_into().unwrap(), ip_address: from_ip, port: from_port };
                        println!("{:05}: Server recieved client hello from static key = {:?}", my_port, client_endpoint);
                        if peer.outgoing_handshake_state.is_none() || contended_noise_is_initiator(&my_root_public_key.into(), &peer.root_public_key) {
                            let start_nonce = rand::random::<u64>() >> 1;
                            start_nonce            .write_to(&mut send_buf1[0..]);
                            PACKET_TAG_SERVER_HELLO.write_to(&mut send_buf1[8..]);
                            let length = incoming_state.write_message(&send_buf1[0..8+1], &mut send_buf2).unwrap();
                            send_sock_msg(&sock, peer_endpoint, &send_buf2[0..length]);

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
                let mut incoming_state: HandshakeState = snow::Builder::new(noise_params.clone())
                    .local_private_key(&my_static_keypair.private).unwrap()
                    .build_responder().unwrap();
                if let Ok(length) = incoming_state.read_message(raw_msg, &mut recv_buf2) {
                    let local_msg = &recv_buf2[0..length];
                    if local_msg == [PACKET_TAG_CLIENT_HELLO] {
                        let client_endpoint = SecureUdpEndpoint { public_key: incoming_state.get_remote_static().unwrap().try_into().unwrap(), ip_address: from_ip, port: from_port };
                        println!("{:05}: Server recieved client hello from unknown peer with static key = {:?}", my_port, client_endpoint);

                        let start_nonce = rand::random::<u64>() >> 1;
                        start_nonce                    .write_to(&mut send_buf1[      ..]);
                        PACKET_TAG_SERVER_UNKNOWN_HELLO.write_to(&mut send_buf1[8     ..]);
                        from_ip                        .write_to(&mut send_buf1[8+1   ..]);
                        from_port                      .write_to(&mut send_buf1[8+1+16..]);
                        let length = incoming_state.write_message(&send_buf1[0..8+1+16+2], &mut send_buf2).unwrap();
                        send_sock_msg(&sock, client_endpoint, &send_buf2[0..length]);

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
    pub fn write_to(&self, buf: &mut [u8]) -> usize {
        self.nonce_ack_latest.write_to(&mut buf[..]);
        self.nonce_ack_field.write_to(&mut buf[64..]);
        128
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

#[derive(Clone, Copy, PartialEq, Eq)]
struct PubKeySig {
    pub_key: PubKeyID,
    sig: TMSig,
}

// agnostic to prevote/precommit - communicated elsewhere
// NOTE: all votes for the same value_id (or nil)
// #[repr(C)]
struct PacketVotes {
    tag:      u8,
    votes_n:  u8, // ALT: split yes_votes, no_votes
    // pad_:     u16, // TODO: useful?
    round:    u32,
    height:   u64,
    value_id: ValueId,
    // TODO: use u16 roster_idxs instead of pub_keys
    votes:    [PubKeySig; 12],
}
const_assert!(size_of::<PacketVotes>() == 1200); // TODO(azmr): exactly how much space is left
                                                 // after noise/nonce/ECC/...?

impl PacketVotes {
    fn write_to(&self, buf: &mut [u8]) -> usize {
        self.tag       .write_to(&mut buf[ 0..]);
        self.votes_n   .write_to(&mut buf[ 1..]);
        self.round     .write_to(&mut buf[ 2..]);
        self.height    .write_to(&mut buf[ 6..]);
        self.value_id.0.write_to(&mut buf[14..]);
        let mut o = 46;
        // NOTE(azmr): slight saving of bytes-on-wire if unused? i.e. initial few times each
        for i in 0..self.votes_n as usize {
            o += &self.votes[i].pub_key.0.write_to(&mut buf[o..]);
            o += &self.votes[i].sig    .0.write_to(&mut buf[o..]);
        }
        o
    }

    pub fn read_from<R: Read>(mut r: R) -> std::io::Result<Self> {
        let mut packet = PacketVotes {
            tag: 0, votes_n: 0, round: 0, height: 0,
            value_id: ValueId::NIL,
            votes: [PubKeySig{ pub_key: PubKeyID::NIL, sig: TMSig::NIL }; 12],
        };
        packet.tag     = r.read_u8()?;
        packet.votes_n = r.read_u8()?;
        packet.round   = r.read_u32::<LittleEndian>()?;
        packet.height  = r.read_u64::<LittleEndian>()?;
        r.read_exact(&mut packet.value_id.0)?;
        for i in 0..packet.votes_n as usize {
            r.read_exact(&mut packet.votes[i].pub_key.0)?;
            r.read_exact(&mut packet.votes[i].sig.0)?;
        }
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
        let mut cumulative_stake = 0;
        let roster : Vec<SortedRosterMember> = static_private_keys.iter().enumerate().map(|(i, sk)| {
            let stake = 2000 * (static_private_keys.len() - 1 - i) as u64;
            cumulative_stake += stake;
            SortedRosterMember { pub_key: PubKeyID(sk.verification_key().into()), stake, cumulative_stake }
        }).collect();
        assert!(roster.is_sorted_by(|a,b| a.stake >= b.stake)); // descending

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
        assert!((None, PubKeyID::NIL) == TMState::proposer_from_height_round(&[], 100, 2, 1));
        for height in 0..8 {
            for round in 0..6 {
                let (Some(i), _) = TMState::proposer_from_height_round(&roster_[..], 100, height, round) else { panic!(); };
                println!("BFT Proposer at {}.{}: {}", height, round, i);
                let (Some(i), _) = TMState::proposer_from_height_round(&roster[..], 100, height, round) else { panic!(); };
                println!("BFT Proposer at {}.{}: {}", height, round, i);
                let (Some(i), _) = TMState::proposer_from_height_round(&roster[..1], 100, height, round) else { panic!(); };
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
}

