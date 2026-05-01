-- Layered entry point for 213.
-- Canonical theoretical layer architecture: lean/E213/ARCHITECTURE.md
--
-- This umbrella file imports the *vertical-layer* foundation modules
-- (Kernel, Firmware, Hypervisor, Meta, App) + key infrastructure.
-- Topical-cluster files under Math/, Physics/ (and the per-layer
-- Tactic/, Tools/, Research/ sub-folders) are NOT imported here en
-- masse — their dependency closures are large and cross-cutting;
-- consumers should import the specific module they need.

-- Kernel (Lean-side scaffolding for 213 — 0 axiom)
import E213.Kernel.Term
import E213.Kernel.Compare
import E213.Kernel.Pair
import E213.Kernel.Rat
import E213.Kernel.Decide
import E213.Kernel.Sound
import E213.Kernel.Demo

-- Firmware (Raw axiom + forced shape uniqueness)
import E213.Firmware.Raw
import E213.Firmware.RawSwap
import E213.Firmware.RawLevels
import E213.Firmware.Atomicity.Five
import E213.Firmware.Atomicity.PairForcing

-- Hypervisor (Lens framework)
import E213.Hypervisor.Lens

-- App (concrete applications)
import E213.App.Simplex

-- Math infrastructure (universal — used by Physics + Research)
import E213.Math.Pigeonhole

-- Tactic / Tools
import E213.Kernel.Tactic.Omega213
import E213.Firmware.Tools.CertChecker
