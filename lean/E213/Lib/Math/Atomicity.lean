import E213.Lib.Math.Atomicity.ArityForcingGeneral

/-! Spec-as-code entry point for `E213.Lib.Math.Atomicity`.

  Lib-side Atomicity facts — generic pigeonhole-style forcing
  arguments that depend on universal Math infrastructure
  (Pigeonhole / Fin) rather than the specific Raw axiom set.

  Theory-side atomicity (Five, PairForcing, NonDecomposable, Alive,
  ArityForcing, PrimitiveSizes) lives in `Theory/Atomicity/` —
  forced shape uniqueness predictions about Raw's atomic structure.

  ## Files (1)

    * `ArityForcingGeneral` — general N < k pigeonhole arity-forcing
      (moved here 2026-05 from `Theory/Atomicity/` since it's a
      universal Fin result, not Raw-axiom-specific)
-/
