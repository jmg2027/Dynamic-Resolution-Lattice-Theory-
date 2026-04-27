import E213.Research.Real213DyadicBracket
import E213.Research.Real213CauchyComplete

/-!
# Research.Real213ConsistentOracle: oracle consistency as a typed
  protocol — the 213-native solution to Cauchy Case C.

## User insight (Phase J Sec 1)

ZFC IVT의 유령은 "어딘가 c가 정확히 존재한다"는 신화에서 온다.
213은 이를 거부하므로, oracle 의 *진동 에러 구간*을 외부 가정으로
끌어오는 대신, **oracle 자체에 protocol 족쇄를 채워야** 한다.

## 정의

`ConsistentOracle db` 는 다음을 보증한다:

- `oracle : DyadicOracle` — bisection의 steering wheel.
- `thresholdN m k : Nat` — query (m, k)에 대한 일관성 임계점.
- `consistency` — n ≥ thresholdN m k 인 모든 step n에서, bracket
  midpoint cut at (m, k) 는 안정 (n_1, n_2 모두 임계점 이상이면
  midCut 값 동일).

즉, oracle 이 임계점 이후에는 cut 응답을 번복하지 않는다는 약속.

## 의의

이 typed protocol 안에서 midSeq는 Cauchy.  사용자 통찰 그대로:
"결과는 궤적 그 자체이지 limit가 아니다" — ConsistentOracle은
궤적이 충분히 안정적임을 보장하는 type-level 계약.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **ConsistentOracle**: an oracle protocol carrying its own
    consistency threshold function.

    The threshold `thresholdN m k` is the step count past which the
    bracket midpoint cut at query (m, k) is no longer flipped.

    Concrete instances supply the threshold formula based on
    target-cut parameters (db.lenNum, db.expE, m, k). -/
structure ConsistentOracle (db : DyadicBracket) where
  oracle : DyadicOracle
  /-- Per-query consistency threshold N(m, k).
      Recommended formula: lenNum * (m + k + 1) — linear in problem
      size, reliable since 2^N grows exponentially. -/
  thresholdN : Nat → Nat → Nat
  /-- For any two steps past the threshold, bracket midpoint cut at
      (m, k) is the same — sequence is stable. -/
  consistency : ∀ m k n1 n2,
    n1 ≥ thresholdN m k → n2 ≥ thresholdN m k →
    (DyadicBracket.bisectN oracle n1 db).midCut m k
    = (DyadicBracket.bisectN oracle n2 db).midCut m k

/-- **The 213-native IVT trajectory**: under a ConsistentOracle,
    the bracket midpoint sequence is a CauchyCutSeq.

    This is the formal payoff of Phase J: the IVT is no longer a
    point-existence claim but a Cauchy trajectory of dyadic
    midpoints, with explicit modulus baked in.  -/
def ConsistentOracle.toCauchyCutSeq {db : DyadicBracket}
    (co : ConsistentOracle db) : CauchyCutSeq where
  cs := fun n => (DyadicBracket.bisectN co.oracle n db).midCut
  N := co.thresholdN
  cauchy := co.consistency

end E213.Research.Real213CutSum
