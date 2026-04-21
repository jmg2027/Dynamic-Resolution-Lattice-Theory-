-- Layered entry point for 213.
--
-- Original 4-layer architecture:
--   Firmware   : E213/Firmware/*.lean   (Raw API)
--   Hypervisor : E213/Hypervisor/*.lean (Lens framework)
--   OS         : E213/OS/*.lean         (axiom-driven theorems)
--   App        : E213/App/*.lean        (applications, e.g. Simplex)
-- Plus:
--   Meta       : E213/Meta/*.lean       (typeclass hierarchies,
--                                        lens catalogue)
--   Tactic     : E213/Tactic/*.lean     (custom macros + elabs)
--   Research   : E213/Research/*.lean   (r5-critique track:
--                                        ZI, Z2, ZOmega witnesses)

-- Firmware
import E213.Firmware.Raw
import E213.Firmware.RawSwap
import E213.Firmware.RawLevels

-- Hypervisor
import E213.Hypervisor.Lens

-- OS
import E213.OS.Pigeonhole
import E213.OS.ArityForcing
import E213.OS.ArityForcingGeneral
import E213.OS.NonDecomposable
import E213.OS.PrimitiveSizes
import E213.OS.Alive
import E213.OS.Atomicity
import E213.OS.PairForcing

-- App
import E213.App.Simplex

-- Meta
import E213.Meta.LensCatalog
import E213.Meta.SelfRecognising

-- Tactic
import E213.Tactic.QuadNorm
import E213.Tactic.IntSquare
import E213.Tactic.DeriveR4Codomain
import E213.Tactic.VerifyR4

-- Research (r5-critique)
import E213.Research.IntHelpers
import E213.Research.ZI
import E213.Research.ZIDomain
import E213.Research.ZIHom
import E213.Research.ZIInstance
import E213.Research.ZSqrt2
import E213.Research.ZSqrt2Domain
import E213.Research.Z2Instance
import E213.Research.ZOmega
import E213.Research.ZOmegaDomain
import E213.Research.ZOmegaInstance
import E213.Research.ZSqrt
import E213.Research.ZSqrtDomain
import E213.Research.ZSqrtInstance
import E213.Research.R5Vacuity
