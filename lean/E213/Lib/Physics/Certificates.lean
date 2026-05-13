import E213.Lib.Physics.Certificates.Checker

/-! Spec-as-code entry point for `E213.Lib.Physics.Certificates`.

  Lean-side certificate verifier mirroring the Rust `Certificate`
  schema (rust-engine/.../alpha_em_bracket.rs).  Each Rust certificate
  is a sequence of bracket / arithmetic / equality steps; `Checker`
  validates them inside Lean against the same atomic constants.

  ## Files (1)

    * `Checker` — `Theory.Tools.CertChecker` — schema mirror + verifier
-/
