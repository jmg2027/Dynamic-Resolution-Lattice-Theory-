//! Certificate emitter — JSON trace of a 213 calculation.
//!
//! Format per `rust-engine/docs/trust-contract.md`:
//!   `Step = Const | Apply | Bound | Cite`.
//! All numbers ℕ as decimal strings.  Hand-rolled JSON (no serde
//! dependency on the runtime path).

use num_bigint::BigUint;

#[derive(Clone, Debug)]
pub enum Step {
    Const { name: String, value: (BigUint, BigUint) },
    Apply { op: String, args: Vec<(BigUint, BigUint)>, result: (BigUint, BigUint) },
    Bound { lhs: (BigUint, BigUint), cmp: Cmp, rhs: (BigUint, BigUint) },
    Cite  { lemma: String },
}

#[derive(Clone, Copy, Debug)]
pub enum Cmp { Lt, Le, Eq }

impl Cmp {
    pub fn as_str(&self) -> &'static str {
        match self { Cmp::Lt => "<", Cmp::Le => "<=", Cmp::Eq => "==" }
    }
}

#[derive(Clone, Debug)]
pub struct Certificate { pub steps: Vec<Step> }

impl Certificate {
    pub fn new() -> Self { Self { steps: vec![] } }
    pub fn push(&mut self, s: Step) -> &mut Self { self.steps.push(s); self }
    pub fn to_json(&self) -> String {
        let mut s = String::from("{\n  \"steps\": [\n");
        for (i, st) in self.steps.iter().enumerate() {
            if i > 0 { s.push_str(",\n"); }
            s.push_str("    "); s.push_str(&step_json(st));
        }
        s.push_str("\n  ]\n}\n"); s
    }
}

impl Default for Certificate { fn default() -> Self { Self::new() } }

fn q_json(q: &(BigUint, BigUint)) -> String {
    format!("[\"{}\", \"{}\"]", q.0, q.1)
}

fn list_json(qs: &[(BigUint, BigUint)]) -> String {
    let parts: Vec<_> = qs.iter().map(q_json).collect();
    format!("[{}]", parts.join(", "))
}

fn step_json(s: &Step) -> String {
    match s {
        Step::Const { name, value } => format!(
            "{{\"kind\":\"Const\",\"name\":\"{name}\",\"value\":{}}}",
            q_json(value)),
        Step::Apply { op, args, result } => format!(
            "{{\"kind\":\"Apply\",\"op\":\"{op}\",\"args\":{},\"result\":{}}}",
            list_json(args), q_json(result)),
        Step::Bound { lhs, cmp, rhs } => format!(
            "{{\"kind\":\"Bound\",\"lhs\":{},\"cmp\":\"{}\",\"rhs\":{}}}",
            q_json(lhs), cmp.as_str(), q_json(rhs)),
        Step::Cite { lemma } => format!(
            "{{\"kind\":\"Cite\",\"lemma\":\"{lemma}\"}}"),
    }
}
