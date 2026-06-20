//! `oxiz-mbqi` — a clean-room quantifier-instantiation engine built around a
//! single soundness invariant: **the engine never concludes `Unsat`**; it
//! only emits sound, guarded, ground instantiation lemmas, and any `Unsat`
//! is the host ground core's. See `DESIGN.md`.
//!
//! Status: M1 (sound enumerative core + never-unsat invariant). M2 adds
//! e-matching + CDQI candidate selection; M3 adds model-based verification
//! for trigger-free quantifiers; M4 ports into OxiZ.

pub mod ccfv;
pub mod cdqi;
pub mod congruence;
pub mod engine;
pub mod ground;
pub mod instantiate;
pub mod ledger;
pub mod model;
pub mod term;
pub mod toy;

pub use ccfv::{match_trigger, match_trigger_multi, Subst};
pub use congruence::{Congruence, FuncApp, Mode, NoCong, TotalView};
pub use engine::{Config, Engine, Verdict};
pub use ledger::{CongruenceSink, GroundLedger, LedgerMark};
pub use instantiate::Quant;
pub use model::{ModelEval, NoModel};
pub use term::{Binding, Sig, TermLang, TermView};
