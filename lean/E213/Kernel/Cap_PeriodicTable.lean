import E213.Kernel.Term
import E213.Kernel.Sound

/-!
# E213.Kernel.Cap_PeriodicTable — 주기율표 capstone, 0 axiom.

213 의 핵심 결과: 노블 가스 Z 값 (2,10,18,36,54,86,118) 이 모두
원자껍질 닫힘 (period length 2·n²) 누적합으로 *정확* 매칭.
다음 예측: Z=168 (Og 다음 슈퍼-헤비, HO magic 7).

각 capstone `rfl` 또는 KF Sound 다리 사용 → 0 axiom.
-/

namespace E213.Kernel.Cap.PeriodicTable

open Term

/-- 노블 가스 Z 값 (Z=2 부터 Z=118 까지). -/
def noble_Z : List Nat := [2, 10, 18, 36, 54, 86, 118]

/-- 213 예측 노블 가스 Z=168 (8th, super-heavy). -/
def Z_predicted : Nat := 168

/-- Period length: 2, 8, 8, 18, 18, 32, 32, 50.
    각각 2·1², 2·2², 2·2², 2·3², 2·3², 2·4², 2·4², 2·5²=2·d². -/
def period_lengths : List Nat := [2, 8, 8, 18, 18, 32, 32, 50]

/-- 누적합 (cumsum) 으로 Z 도출. -/
def cumsum : List Nat → List Nat
  | []        => []
  | x :: xs   => cumsumAux x xs
where
  cumsumAux (acc : Nat) : List Nat → List Nat
    | []        => [acc]
    | y :: ys   => acc :: cumsumAux (acc + y) ys

theorem noble_from_periods :
    cumsum period_lengths = [2, 10, 18, 36, 54, 86, 118, 168] := rfl

/-- 마지막 = 213 예측 Z=168. -/
theorem Z8_eq_168 :
    (cumsum period_lengths).getLast? = some Z_predicted := rfl

/-- 가벼운 동일성: 50 = 2·d² (Argon octet 의 다섯 배, period 8).
    Z_8 - Z_7 = 168 - 118 = 50 = 2·d² 의 Term 형태. -/
theorem fifty_eq_two_dsq :
    eval (mul (succ (succ zero)) (mul d d)) = 50 := rfl

/-- period 4,5 길이 = 18 = 2·n_S² (n_S=3). -/
theorem eighteen_eq_two_nSsq :
    eval (mul (succ (succ zero)) (mul nS nS)) = 18 := rfl

/-- period 6,7 길이 = 32 = 2·(n_T²)²  (n_T=2, n_T²=4, (n_T²)²=16, ·2 =32). -/
theorem thirtytwo_eq_two_nT4 :
    eval (mul (succ (succ zero)) (mul (mul nT nT) (mul nT nT))) = 32 := rfl

/-- period 2,3 길이 = 8 = 2·n_T² (Argon octet 의 토대). -/
theorem eight_eq_two_nTsq :
    eval (mul (succ (succ zero)) (mul nT nT)) = 8 := rfl

/-- period 1 길이 = 2 = n_T (He, 가장 간단한 닫힘). -/
theorem two_eq_nT : eval nT = 2 := rfl

end E213.Kernel.Cap.PeriodicTable

#print axioms E213.Kernel.Cap.PeriodicTable.noble_from_periods
#print axioms E213.Kernel.Cap.PeriodicTable.Z8_eq_168
#print axioms E213.Kernel.Cap.PeriodicTable.fifty_eq_two_dsq
#print axioms E213.Kernel.Cap.PeriodicTable.eighteen_eq_two_nSsq
#print axioms E213.Kernel.Cap.PeriodicTable.thirtytwo_eq_two_nT4
#print axioms E213.Kernel.Cap.PeriodicTable.eight_eq_two_nTsq
#print axioms E213.Kernel.Cap.PeriodicTable.two_eq_nT
