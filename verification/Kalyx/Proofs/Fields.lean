module

public import Kalyx.Statements.Fields
import Mathlib.Data.Rat.Sqrt
import Mathlib.FieldTheory.KummerPolynomial

/-!
# Proofs of the statements about the coefficient fields

One theorem for each registered statement of `Kalyx.Statements.Fields`, whose
type is exactly that statement. The lemmas before them are private to this
module:

* the outcomes that the checks of the limits admit for a domain outcome that
  is a value, a fault or `ResourceLimit` (`admits_value`, `admits_fault`,
  `admits_limit`);
* for the rationals, the integers, the residue rings and the prime fields,
  the canonical forms and the operations under their interpretations;
* the reduction of the rationals modulo a prime as a ring homomorphism on the
  rationals whose denominator the prime does not divide (`localSubring`,
  `reduceHom`);
* for the dense rational polynomials of the number fields, the polynomial
  that a list denotes under the sum, the difference, the product and the
  removal of trailing zeros, the invariant of the long division
  (`divMod_spec`) and that of the extended Euclidean algorithm
  (`euclid_spec`), from which the canonical forms and the inverse of the
  number fields follow;
* that `x² + 1` and `x² - 2` are irreducible over `ℚ`, since neither `-1` nor
  `2` is the square of a rational.

The examples about given values are decided by evaluation in the kernel
(`decide +kernel`).
-/

namespace Kalyx.Proofs.Fields

open Kalyx.Spec.Fields Kalyx.Statements.Fields Polynomial

/-! ## Zero tests and the checks of the limits -/

/-- The answer of a decidable test is `zero` exactly when the test holds and
`nonzero` exactly when it does not. -/
private theorem ofDecide_exact {U : Type} (P Q : Prop) [Decidable P] (h : P ↔ Q) :
    (Outcome.value (ZeroTest.ofDecide P : ZeroTest U) = .value .zero ↔ Q) ∧
      (Outcome.value (ZeroTest.ofDecide P : ZeroTest U) = .value .nonzero ↔ ¬Q) := by
  unfold ZeroTest.ofDecide
  split <;> simp_all

/-- Where the domain outcome is a value whose estimate and bits are within the
limit, the value is the only admitted outcome. -/
private theorem admits_value {α : Type} (c : SizeCheck α) (f : LimitField) (v : α)
    (h1 : ¬c.estimateAbove) (h2 : ¬c.above v) (o : Outcome α) :
    c.Admits f (.value v) o ↔ o = .value v := by
  cases o with
  | value a =>
    simp only [SizeCheck.Admits, Outcome.value.injEq]
    constructor
    · rintro ⟨rfl, -⟩; rfl
    · rintro rfl; exact ⟨rfl, h2⟩
  | fault e => simp [SizeCheck.Admits]
  | resourceLimit l => simp [SizeCheck.Admits, h1, h2]

/-- A fault of the domain layer is the only admitted outcome, under every
limit. -/
private theorem admits_fault {α : Type} (c : SizeCheck α) (f : LimitField) (e : FieldError)
    (o : Outcome α) : c.Admits f (.fault e) o ↔ o = .fault e := by
  cases o <;> simp [SizeCheck.Admits, eq_comm]

/-- A `ResourceLimit` of the domain layer is the only admitted outcome. -/
private theorem admits_limit {α : Type} (c : SizeCheck α) (f l : LimitField) (o : Outcome α) :
    c.Admits f (.resourceLimit l) o ↔ o = .resourceLimit l := by
  cases o <;> simp [SizeCheck.Admits, eq_comm]

/-! ## The rationals -/

/-- The fraction of a rational number is reduced. -/
private theorem ofRat_reduced (q : ℚ) : (Fraction.ofRat q).Reduced := by
  refine ⟨Int.natCast_pos.mpr q.pos, ?_⟩
  show Nat.gcd q.num.natAbs (q.den : ℤ).natAbs = 1
  rw [Int.natAbs_natCast]
  exact q.reduced

/-- The fraction of a rational number denotes it. -/
private theorem ofRat_interpret (q : ℚ) : (Fraction.ofRat q).interpret = q := by
  simp [Fraction.ofRat, Fraction.interpret, Rat.num_div_den]

/-- A reduced fraction is the fraction of the number that it denotes. -/
private theorem ofRat_interpret_of_reduced {f : Fraction} (h : f.Reduced) :
    Fraction.ofRat f.interpret = f := by
  obtain ⟨num, den⟩ := f
  obtain ⟨hd, hg⟩ := h
  have hc : Nat.Coprime num.natAbs den.natAbs := hg
  simp only [Fraction.ofRat, Fraction.interpret, Fraction.mk.injEq]
  exact ⟨Rat.num_div_eq_of_coprime hd hc, Rat.den_div_eq_of_coprime hd hc⟩

/-- Reduced fractions are unique. -/
private theorem rat_unique (p : Rationals) : (Rationals.model p).Unique := by
  intro r s hr hs h
  calc r = Fraction.ofRat r.interpret := (ofRat_interpret_of_reduced hr).symm
    _ = Fraction.ofRat s.interpret := congrArg Fraction.ofRat h
    _ = s := ofRat_interpret_of_reduced hs

/-- Every rational has a reduced fraction. -/
private theorem rat_complete (p : Rationals) : (Rationals.model p).Complete :=
  fun q => ⟨Fraction.ofRat q, ofRat_reduced q, ofRat_interpret q⟩

/-- The value of the fraction of `q` is a canonical value that denotes `q`. -/
private theorem rat_yields (p : Rationals) (q : ℚ) :
    Rationals.model.Yields p (.value (Fraction.ofRat q)) q :=
  ⟨_, rfl, ofRat_reduced q, ofRat_interpret q⟩

/-- The fraction `n/1` is reduced and denotes `n`. -/
private theorem int_fraction (n : ℤ) :
    Fraction.Reduced ⟨n, 1⟩ ∧ Fraction.interpret ⟨n, 1⟩ = n :=
  ⟨⟨one_pos, by simp⟩, by simp [Fraction.interpret]⟩

/-- The ring laws of the rationals. -/
private theorem rat_ringLaws : RingLaws Rationals.field.toCoefficientRing Rationals.model where
  unique := rat_unique
  zero _ := ⟨(int_fraction 0).1, by simp [Rationals.field, Rationals.model, Fraction.interpret]⟩
  one _ := ⟨(int_fraction 1).1, by simp [Rationals.field, Rationals.model, Fraction.interpret]⟩
  fromInteger _ n := int_fraction n
  negate p a _ := rat_yields p (-a.interpret)
  add p a b _ _ := rat_yields p (a.interpret + b.interpret)
  subtract p a b _ _ := rat_yields p (a.interpret - b.interpret)
  multiply p a b _ _ := rat_yields p (a.interpret * b.interpret)

/-- The field laws of the rationals. -/
private theorem rat_fieldLaws : FieldLaws Rationals.field Rationals.model where
  inverse p a _ ha := by
    change a.interpret ≠ 0 at ha
    refine ⟨Fraction.ofRat a.interpret⁻¹, ?_, ofRat_reduced _, ?_⟩
    · simp [Rationals.field, RatUnary.exact, ratInvOp, ha, Outcome.map]
    · show a.interpret * (Fraction.ofRat a.interpret⁻¹).interpret = 1
      rw [ofRat_interpret, mul_inv_cancel₀ ha]
  inverse_zero p a _ ha := by
    change a.interpret = 0 at ha
    simp [Rationals.field, RatUnary.exact, ratInvOp, ha, Outcome.map]
  divide p a b _ _ hb := by
    change b.interpret ≠ 0 at hb
    refine ⟨Fraction.ofRat (a.interpret / b.interpret), ?_, ofRat_reduced _, ?_⟩
    · simp [Rationals.field, RatOp.exact, ratDivOp, ratDiv, FieldError.lift, hb, Outcome.map]
    · show (Fraction.ofRat (a.interpret / b.interpret)).interpret * b.interpret = a.interpret
      rw [ofRat_interpret, div_mul_cancel₀ _ hb]
  divide_zero p a b _ _ hb := by
    change b.interpret = 0 at hb
    simp [Rationals.field, RatOp.exact, ratDivOp, ratDiv, FieldError.lift, hb, Outcome.map]

/-- The zero test of the rationals is exact. -/
private theorem rat_zeroTestExact :
    ZeroTestExact Rationals.field.toCoefficientRing Rationals.model :=
  ⟨fun _ a _ => (ofDecide_exact (a.interpret = 0) _ Iff.rfl).1,
    fun _ a _ => (ofDecide_exact (a.interpret = 0) _ Iff.rfl).2⟩

/-! ## The integers -/

/-- The ring laws of the integers, each its own canonical form. -/
private theorem int_ringLaws : RingLaws Integers.ring.toCoefficientRing Integers.model where
  unique _ _ _ _ _ h := h
  zero _ := ⟨trivial, rfl⟩
  one _ := ⟨trivial, rfl⟩
  fromInteger _ _ := ⟨trivial, Int.cast_id.symm⟩
  negate _ a _ := ⟨-a, rfl, trivial, rfl⟩
  add _ a b _ _ := ⟨a + b, rfl, trivial, rfl⟩
  subtract _ a b _ _ := ⟨a - b, rfl, trivial, rfl⟩
  multiply _ a b _ _ := ⟨a * b, rfl, trivial, rfl⟩

/-- The laws of exact division of the integers. -/
private theorem int_exactDivisionLaws : ExactDivisionLaws Integers.ring Integers.model where
  exact _ a b _ _ hb hdvd := by
    change b ≠ 0 at hb
    change b ∣ a at hdvd
    exact ⟨a / b, by simp [Integers.ring, exactDivOp, exactDiv, FieldError.lift, hb, hdvd],
      trivial, (Int.mul_ediv_cancel' hdvd).symm⟩
  inexact _ a b _ _ hb hdvd := by
    change b ≠ 0 at hb
    change ¬b ∣ a at hdvd
    simp [Integers.ring, exactDivOp, exactDiv, FieldError.lift, hb, hdvd]
  divide_zero _ a b _ _ hb := by
    change b = 0 at hb
    simp [Integers.ring, exactDivOp, exactDiv, FieldError.lift, hb]

/-- The zero test of the integers is exact. -/
private theorem int_zeroTestExact : ZeroTestExact Integers.ring.toCoefficientRing Integers.model :=
  ⟨fun _ a _ => (ofDecide_exact (a = 0) _ Iff.rfl).1,
    fun _ a _ => (ofDecide_exact (a = 0) _ Iff.rfl).2⟩

/-! ## The residue rings -/

/-- A residue below the modulus passes the residue test. -/
private theorem residue_of_lt {α : Type} (R : ResidueRing) {a : ℕ} (h : a < R.modulus)
    (next : ZMod R.modulus → Outcome α) : R.residue a next = next a :=
  ite_eq_left h

/-- The least nonnegative residue of a class is a canonical value that
denotes it. -/
private theorem residue_yields (R : ResidueRing) (x : ZMod R.modulus) :
    ResidueRing.model.Yields R (.value x.val) x :=
  ⟨x.val, rfl, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩

/-- A ring operation on two residues below the modulus. -/
private theorem residue_op (R : ResidueRing) (op : ResidueOp) {a b : ℕ}
    (ha : a < R.modulus) (hb : b < R.modulus) :
    R.op op a b = .value (op.value (a : ZMod R.modulus) b).val := by
  rw [ResidueRing.op, residue_of_lt R ha, residue_of_lt R hb]
  rfl

/-- The inverse of a residue below the modulus. -/
private theorem residue_unitInverse (μ : ResidueRing → ℕ → Storage) (R : ResidueRing) {a : ℕ}
    (ha : a < R.modulus) :
    (ResidueRing.ring μ).unitInverse R a =
      (residueInverseOp R.modulus (a : ZMod R.modulus)).map (UnitInverse.map ZMod.val) :=
  residue_of_lt R ha fun x => (residueInverseOp R.modulus x).map (UnitInverse.map ZMod.val)

/-- Residues below the modulus are unique. -/
private theorem residue_unique (R : ResidueRing) : (ResidueRing.model R).Unique := by
  intro r s hr hs h
  change r < (R.modulus : ℕ) at hr
  change s < (R.modulus : ℕ) at hs
  change (r : ZMod R.modulus) = s at h
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hr, ZMod.val_cast_of_lt hs] at h'

/-- The ring laws of the residue rings. -/
private theorem residue_ringLaws (μ : ResidueRing → ℕ → Storage) :
    RingLaws (ResidueRing.ring μ).toCoefficientRing ResidueRing.model where
  unique := residue_unique
  zero R := ⟨R.modulus.pos, Nat.cast_zero⟩
  one _ := ⟨ZMod.val_lt _, ZMod.natCast_zmod_val _⟩
  fromInteger _ _ := ⟨ZMod.val_lt _, ZMod.natCast_zmod_val _⟩
  negate R a ha := by
    show ResidueRing.model.Yields R (R.residue a fun x => .value (-x).val) _
    rw [residue_of_lt R ha]
    exact residue_yields R _
  add R a b ha hb := by
    show ResidueRing.model.Yields R (R.op .add a b) _
    rw [residue_op R .add ha hb]
    exact residue_yields R _
  subtract R a b ha hb := by
    show ResidueRing.model.Yields R (R.op .sub a b) _
    rw [residue_op R .sub ha hb]
    exact residue_yields R _
  multiply R a b ha hb := by
    show ResidueRing.model.Yields R (R.op .mul a b) _
    rw [residue_op R .mul ha hb]
    exact residue_yields R _

/-- A residue class is a unit exactly when it is prime to the modulus. -/
private theorem isUnit_iff_gcd (n : ℕ) [NeZero n] (a : ZMod n) :
    IsUnit a ↔ Nat.gcd a.val n = 1 := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  exact (ZMod.isUnit_iff_coprime a.val n).trans Nat.coprime_iff_gcd_eq_one

/-- A unit has its inverse. -/
private theorem residueInverseOp_unit (n : ℕ) [NeZero n] (x : ZMod n) (hx : IsUnit x) :
    residueInverseOp n x = .value (.unit x⁻¹) ∧ x * x⁻¹ = 1 := by
  have hg := (isUnit_iff_gcd n x).mp hx
  have h0 : ¬(x = 0 ∧ 1 < n) := by
    rintro ⟨rfl, hn⟩
    have : Fact (1 < n) := ⟨hn⟩
    exact not_isUnit_zero hx
  refine ⟨?_, ?_⟩
  · rw [residueInverseOp, residueInverse, ite_eq_right h0, ite_eq_left hg]
    rfl
  · rw [ZMod.mul_inv_eq_gcd, hg, Nat.cast_one]

/-- A nonzero residue that is not a unit has the result state `nonUnit`. -/
private theorem residueInverseOp_nonUnit (n : ℕ) [NeZero n] (x : ZMod n) (h0 : x ≠ 0)
    (hx : ¬IsUnit x) : residueInverseOp n x = .value (.nonUnit (Nat.gcd x.val n)) := by
  rw [residueInverseOp, residueInverse, ite_eq_right (fun h => h0 h.1),
    ite_eq_right (fun hg => hx ((isUnit_iff_gcd n x).mpr hg))]
  rfl

/-- For a modulus above one the inverse of zero is `DivisionByZero`. -/
private theorem residueInverseOp_zero (n : ℕ) (hn : 1 < n) :
    residueInverseOp n 0 = .fault .divisionByZero := by
  rw [residueInverseOp, residueInverse, ite_eq_left ⟨rfl, hn⟩]
  rfl

/-- Zero is a unit modulo one, so a modulus where it is not is above one. -/
private theorem one_lt_of_not_isUnit_zero (n : ℕ) [NeZero n] (h : ¬IsUnit (0 : ZMod n)) :
    1 < n := by
  by_contra h1
  have : Subsingleton (ZMod n) := ZMod.subsingleton_iff.mpr (by have := NeZero.pos n; omega)
  exact h (isUnit_of_subsingleton _)

/-- The laws of the inverse of a unit of the residue rings. -/
private theorem residue_unitInverseLaws (μ : ResidueRing → ℕ → Storage) :
    UnitInverseLaws (ResidueRing.ring μ) ResidueRing.model where
  unit R a ha hu := by
    change a < (R.modulus : ℕ) at ha
    change IsUnit (a : ZMod R.modulus) at hu
    obtain ⟨h1, h2⟩ := residueInverseOp_unit _ _ hu
    refine ⟨((a : ZMod R.modulus)⁻¹).val, ?_, ZMod.val_lt _, ?_⟩
    · rw [residue_unitInverse μ R ha, h1]
      rfl
    · show (a : ZMod R.modulus) * (((a : ZMod R.modulus)⁻¹).val : ZMod R.modulus) = 1
      rw [ZMod.natCast_zmod_val, h2]
  nonUnit R a ha hu h0 := by
    change a < (R.modulus : ℕ) at ha
    change ¬IsUnit (a : ZMod R.modulus) at hu
    change (a : ZMod R.modulus) ≠ 0 at h0
    exact ⟨_, by rw [residue_unitInverse μ R ha, residueInverseOp_nonUnit _ _ h0 hu]; rfl⟩
  zero R a ha hu h0 := by
    change a < (R.modulus : ℕ) at ha
    change ¬IsUnit (a : ZMod R.modulus) at hu
    change (a : ZMod R.modulus) = 0 at h0
    rw [h0] at hu
    rw [residue_unitInverse μ R ha, h0, residueInverseOp_zero _ (one_lt_of_not_isUnit_zero _ hu)]
    rfl

/-- The zero test of the residue rings is exact. -/
private theorem residue_zeroTestExact (μ : ResidueRing → ℕ → Storage) :
    ZeroTestExact (ResidueRing.ring μ).toCoefficientRing ResidueRing.model where
  zero R a ha := by
    show R.residue a (fun x => .value (residueIsZero R.modulus x)) = _ ↔ _
    rw [residue_of_lt R ha]
    exact (ofDecide_exact ((a : ZMod R.modulus) = 0) _ Iff.rfl).1
  nonzero R a ha := by
    show R.residue a (fun x => .value (residueIsZero R.modulus x)) = _ ↔ _
    rw [residue_of_lt R ha]
    exact (ofDecide_exact ((a : ZMod R.modulus) = 0) _ Iff.rfl).2

/-! ## The prime fields -/

/-- A residue below the modulus passes the residue test. -/
private theorem prime_require {α : Type} (F : PrimeField) {a : PrimeResidue}
    (h : a.value < F.modulus) (next : Outcome α) : F.requireResidue a next = next :=
  ite_eq_left h

/-- The least nonnegative residue of a class is canonical and denotes it. -/
private theorem prime_ofZMod (F : PrimeField) (x : ZMod F.modulus) :
    (PrimeField.model F).canonical (F.ofZMod x) ∧
      (PrimeField.model F).interpret (F.ofZMod x) = x := by
  have : NeZero F.modulus := ⟨F.prime.ne_zero⟩
  exact ⟨ZMod.val_lt x, ZMod.natCast_zmod_val x⟩

/-- The least nonnegative residue of a class is a canonical value that
denotes it. -/
private theorem prime_yields (F : PrimeField) (x : ZMod F.modulus) :
    PrimeField.model.Yields F (.value (F.ofZMod x)) x :=
  ⟨_, rfl, prime_ofZMod F x⟩

/-- A method of one residue below the modulus. -/
private theorem prime_unary (F : PrimeField) (op : ZMod F.modulus → Outcome (ZMod F.modulus))
    {a : PrimeResidue} (ha : a.value < F.modulus) :
    F.unary op a = (op (F.toZMod a)).map F.ofZMod :=
  prime_require F ha _

/-- A method of two residues below the modulus. -/
private theorem prime_binary (F : PrimeField)
    (op : ZMod F.modulus → ZMod F.modulus → Outcome (ZMod F.modulus)) {a b : PrimeResidue}
    (ha : a.value < F.modulus) (hb : b.value < F.modulus) :
    F.binary op a b = (op (F.toZMod a) (F.toZMod b)).map F.ofZMod := by
  rw [PrimeField.binary, prime_require F ha, prime_require F hb]

/-- A nonzero class modulo a prime multiplies with its inverse to one. -/
private theorem zmod_mul_inv (p : ℕ) (hp : p.Prime) (x : ZMod p) (hx : x ≠ 0) :
    x * x⁻¹ = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hval : x.val ≠ 0 := fun h0 => hx ((ZMod.val_eq_zero x).mp h0)
  have hcop : Nat.Coprime x.val p := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd =>
      hval (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt x))
  rw [ZMod.mul_inv_eq_gcd, Nat.Coprime.gcd_eq_one hcop, Nat.cast_one]

/-- A nonzero class of a prime field multiplies with its inverse to one. -/
private theorem prime_mul_inv (F : PrimeField) (x : ZMod F.modulus) (hx : x ≠ 0) :
    x * x⁻¹ = 1 :=
  zmod_mul_inv F.modulus F.prime x hx

/-- Residues below the modulus are unique. -/
private theorem prime_unique (F : PrimeField) : (PrimeField.model F).Unique := by
  intro r s hr hs h
  change r.value < F.modulus at hr
  change s.value < F.modulus at hs
  change (r.value : ZMod F.modulus) = s.value at h
  have h' := congrArg ZMod.val h
  rw [ZMod.val_cast_of_lt hr, ZMod.val_cast_of_lt hs] at h'
  cases r
  cases s
  cases h'
  rfl

/-- The ring laws of the prime fields. -/
private theorem prime_ringLaws : RingLaws PrimeField.field.toCoefficientRing PrimeField.model where
  unique := prime_unique
  zero F := ⟨F.prime.pos, Nat.cast_zero⟩
  one F := ⟨F.prime.one_lt, Nat.cast_one⟩
  fromInteger F n := by
    have hp : (0 : ℤ) < F.modulus := by exact_mod_cast F.prime.pos
    have h1 := Int.emod_nonneg n hp.ne'
    have h2 := Int.emod_lt_of_pos n hp
    refine ⟨?_, ?_⟩
    · show (n % (F.modulus : ℤ)).toNat < F.modulus
      omega
    · show (((n % (F.modulus : ℤ)).toNat : ℕ) : ZMod F.modulus) = n
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h1, ZMod.intCast_mod]
  negate F a ha := by
    show PrimeField.model.Yields F (F.unary (fun x => .value (-x)) a) _
    rw [prime_unary F _ ha]
    exact prime_yields F _
  add F a b ha hb := by
    show PrimeField.model.Yields F (F.binary (fun x y => .value (x + y)) a b) _
    rw [prime_binary F _ ha hb]
    exact prime_yields F _
  subtract F a b ha hb := by
    show PrimeField.model.Yields F (F.binary (fun x y => .value (x - y)) a b) _
    rw [prime_binary F _ ha hb]
    exact prime_yields F _
  multiply F a b ha hb := by
    show PrimeField.model.Yields F (F.binary (fun x y => .value (x * y)) a b) _
    rw [prime_binary F _ ha hb]
    exact prime_yields F _

/-- The field laws of the prime fields. -/
private theorem prime_fieldLaws : FieldLaws PrimeField.field PrimeField.model where
  inverse F a ha hx := by
    change F.toZMod a ≠ 0 at hx
    refine ⟨F.ofZMod (F.toZMod a)⁻¹, ?_, (prime_ofZMod F _).1, ?_⟩
    · show F.unary (primeInverseOp F.modulus) a = _
      rw [prime_unary F _ ha, primeInverseOp, primeInverse, ite_eq_right hx]
      rfl
    · rw [(prime_ofZMod F _).2]
      exact prime_mul_inv F _ hx
  inverse_zero F a ha hx := by
    change F.toZMod a = 0 at hx
    show F.unary (primeInverseOp F.modulus) a = _
    rw [prime_unary F _ ha, primeInverseOp, primeInverse, ite_eq_left hx]
    rfl
  divide F a b ha hb hy := by
    change F.toZMod b ≠ 0 at hy
    refine ⟨F.ofZMod (F.toZMod a * (F.toZMod b)⁻¹), ?_, (prime_ofZMod F _).1, ?_⟩
    · show F.binary (primeDivOp F.modulus) a b = _
      rw [prime_binary F _ ha hb, primeDivOp, primeDiv, primeInverse, ite_eq_right hy]
      rfl
    · rw [(prime_ofZMod F _).2]
      show F.toZMod a * (F.toZMod b)⁻¹ * F.toZMod b = F.toZMod a
      rw [mul_assoc, mul_comm _ (F.toZMod b), prime_mul_inv F _ hy, mul_one]
  divide_zero F a b ha hb hy := by
    change F.toZMod b = 0 at hy
    show F.binary (primeDivOp F.modulus) a b = _
    rw [prime_binary F _ ha hb, primeDivOp, primeDiv, primeInverse, ite_eq_left hy]
    rfl

/-- The zero test of the prime fields is exact. -/
private theorem prime_zeroTestExact :
    ZeroTestExact PrimeField.field.toCoefficientRing PrimeField.model where
  zero F a ha := by
    show F.requireResidue a (.value (primeIsZero F.modulus (F.toZMod a))) = _ ↔ _
    rw [prime_require F ha]
    exact (ofDecide_exact (F.toZMod a = 0) _ Iff.rfl).1
  nonzero F a ha := by
    show F.requireResidue a (.value (primeIsZero F.modulus (F.toZMod a))) = _ ↔ _
    rw [prime_require F ha]
    exact (ofDecide_exact (F.toZMod a = 0) _ Iff.rfl).2

/-- The prime field `𝔽_7`. -/
private def seven : PrimeField := ⟨7, by norm_num, by unfold WordModulus; norm_num⟩

/-- The constructor builds `𝔽_7` from `7`. -/
private theorem new_seven : PrimeField.new 7 = .built seven := by
  unfold PrimeField.new
  rw [dite_eq_left ⟨seven.prime, seven.word⟩]
  rfl

/-! ## The reduction of the rationals modulo a prime -/

/-- A total homomorphism is defined everywhere. -/
private theorem ofRingHom_apply {K L : Type} [CommRing K] [CommRing L] (f : K →+* L) (x : K) :
    (PartialHom.ofRingHom f).apply x = some (f x) := by
  unfold PartialHom.apply
  rw [dite_eq_left (show x ∈ (PartialHom.ofRingHom f).domain from Subring.mem_top x)]
  rfl

section Reduction

variable (p : ℕ) [hp : Fact p.Prime]

/-- The rationals whose denominator in lowest terms the prime `p` does not
divide. -/
private def localSubring : Subring ℚ where
  carrier := {q | ¬p ∣ q.den}
  mul_mem' {a b} ha hb h := (hp.out.dvd_mul.mp (h.trans (Rat.mul_den_dvd a b))).elim ha hb
  one_mem' := by simp [hp.out.ne_one]
  add_mem' {a b} ha hb h := (hp.out.dvd_mul.mp (h.trans (Rat.add_den_dvd a b))).elim ha hb
  zero_mem' := by simp [hp.out.ne_one]
  neg_mem' {a} ha := by simpa using ha

/-- A rational `q` of the subring with `q d = n`: its reduction times `d` is
`n`. -/
private theorem reduce_mul (q : ℚ) (hq : ¬p ∣ q.den) (n : ℤ) (d : ℕ) (h : q * d = n) :
    (q.num : ZMod p) * (q.den : ZMod p)⁻¹ * d = n := by
  have hden := zmod_mul_inv p hp.out (q.den : ZMod p) (by rwa [Ne, ZMod.natCast_eq_zero_iff])
  have hz : q.num * (d : ℤ) = n * q.den := by
    have : (q.num : ℚ) * d = n * q.den := by rw [← h, ← Rat.mul_den_eq_num]; ring
    exact_mod_cast this
  have hz' : (q.num : ZMod p) * d = n * q.den := by
    have := congrArg (Int.cast : ℤ → ZMod p) hz
    push_cast at this
    exact this
  linear_combination (q.den : ZMod p)⁻¹ * hz' + (n : ZMod p) * hden

/-- A factor with an inverse cancels. -/
private theorem zmod_cancel {n : ℕ} (D z₁ z₂ : ZMod n) (hD : D * D⁻¹ = 1)
    (h : z₁ * D = z₂ * D) : z₁ = z₂ := by
  linear_combination D⁻¹ * h - (z₁ - z₂) * hD

/-- The product of the denominators of two rationals of the subring has an
inverse. -/
private theorem den_mul_inv (x y : localSubring p) :
    ((x.1.den * y.1.den : ℕ) : ZMod p) * ((x.1.den * y.1.den : ℕ) : ZMod p)⁻¹ = 1 :=
  zmod_mul_inv p hp.out _ (by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => (hp.out.dvd_mul.mp h).elim x.2 y.2)

/-- The reduction modulo `p` as a ring homomorphism on `localSubring p`. -/
private def reduceHom : localSubring p →+* ZMod p where
  toFun x := (x.1.num : ZMod p) * (x.1.den : ZMod p)⁻¹
  map_one' := by
    show ((1 : ℚ).num : ZMod p) * ((1 : ℚ).den : ZMod p)⁻¹ = 1
    rw [Rat.num_one, Rat.den_one, Int.cast_one, Nat.cast_one,
      ZMod.inv_eq_of_mul_eq_one p 1 1 (mul_one 1), mul_one]
  map_mul' x y := by
    refine zmod_cancel _ _ _ (den_mul_inv p x y) ?_
    have hxy := reduce_mul p (x * y).1 (x * y).2 (x.1.num * y.1.num) (x.1.den * y.1.den) (by
      rw [Subring.coe_mul]
      push_cast
      rw [← Rat.mul_den_eq_num x.1, ← Rat.mul_den_eq_num y.1]
      ring)
    have hx := reduce_mul p x.1 x.2 x.1.num x.1.den (Rat.mul_den_eq_num x.1)
    have hy := reduce_mul p y.1 y.2 y.1.num y.1.den (Rat.mul_den_eq_num y.1)
    push_cast at hxy hx hy ⊢
    linear_combination hxy - (y.1.num : ZMod p) * hx -
      (x.1.num : ZMod p) * (x.1.den : ZMod p)⁻¹ * (x.1.den : ZMod p) * hy
  map_zero' := by
    show ((0 : ℚ).num : ZMod p) * ((0 : ℚ).den : ZMod p)⁻¹ = 0
    rw [Rat.num_zero, Int.cast_zero, zero_mul]
  map_add' x y := by
    refine zmod_cancel _ _ _ (den_mul_inv p x y) ?_
    have hxy := reduce_mul p (x + y).1 (x + y).2 (x.1.num * y.1.den + y.1.num * x.1.den)
      (x.1.den * y.1.den) (by
        rw [Subring.coe_add]
        push_cast
        rw [← Rat.mul_den_eq_num x.1, ← Rat.mul_den_eq_num y.1]
        ring)
    have hx := reduce_mul p x.1 x.2 x.1.num x.1.den (Rat.mul_den_eq_num x.1)
    have hy := reduce_mul p y.1 y.2 y.1.num y.1.den (Rat.mul_den_eq_num y.1)
    push_cast at hxy hx hy ⊢
    linear_combination hxy - (y.1.den : ZMod p) * hx - (x.1.den : ZMod p) * hy

end Reduction

/-- The reduction of the rationals into a prime field is a partial
homomorphism on the rationals whose denominator its prime does not divide. -/
private theorem toPrimeField_partialOn (F : PrimeField) :
    Rationals.toPrimeField.PartialOn Rationals.model PrimeField.model ⟨⟩ F
      fun q => ¬F.modulus ∣ q.den := by
  have : Fact F.modulus.Prime := ⟨F.prime⟩
  refine ⟨⟨localSubring F.modulus, reduceHom F.modulus⟩, fun _ => Iff.rfl, ?_⟩
  intro x _
  by_cases h : F.modulus ∣ x.interpret.den
  · have hn : PartialHom.apply ⟨localSubring F.modulus, reduceHom F.modulus⟩ x.interpret =
        none := dite_eq_right fun hx => hx h
    rw [Rationals.model, hn]
    show (ratReduceOp _ _).map _ = _
    rw [ratReduceOp, ratReduce, ite_eq_left h]
    rfl
  · have hn : PartialHom.apply ⟨localSubring F.modulus, reduceHom F.modulus⟩ x.interpret =
        some ((x.interpret.num : ZMod F.modulus) * (x.interpret.den : ZMod F.modulus)⁻¹) :=
      dite_eq_left h
    rw [Rationals.model, hn]
    refine ⟨_, ?_, prime_ofZMod F _⟩
    show (ratReduceOp _ _).map _ = _
    rw [ratReduceOp, ratReduce, ite_eq_right h]
    rfl

/-! ## Dense rational polynomials -/

section QPoly

open QPoly

/-- The coefficients of the polynomial of a list are its entries. -/
private theorem coeff_toPoly (l : List ℚ) (i : ℕ) : (toPoly l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [toPoly]
  | cons c l ih => cases i <;> simp [toPoly, ih]

/-- The sum of lists denotes the sum of their polynomials. -/
private theorem toPoly_add (p q : List ℚ) : toPoly (QPoly.add p q) = toPoly p + toPoly q := by
  induction p generalizing q with
  | nil => simp [QPoly.add, toPoly]
  | cons a p ih =>
    cases q with
    | nil => simp [QPoly.add, toPoly]
    | cons b q =>
      simp only [QPoly.add, toPoly, ih, map_add]
      ring

/-- The product with a constant. -/
private theorem toPoly_scale (c : ℚ) (p : List ℚ) : toPoly (scale c p) = C c * toPoly p := by
  induction p with
  | nil => simp [scale, toPoly]
  | cons a p ih =>
    simp only [scale, List.map_cons] at ih ⊢
    simp only [toPoly, ih, map_mul]
    ring

/-- The difference. -/
private theorem toPoly_sub (p q : List ℚ) : toPoly (QPoly.sub p q) = toPoly p - toPoly q := by
  rw [QPoly.sub, toPoly_add, toPoly_scale, map_neg, map_one, neg_one_mul, sub_eq_add_neg]

/-- The product. -/
private theorem toPoly_mul (p q : List ℚ) : toPoly (QPoly.mul p q) = toPoly p * toPoly q := by
  induction p with
  | nil => simp [QPoly.mul, toPoly]
  | cons a p ih =>
    simp only [QPoly.mul, toPoly_add, toPoly_scale, toPoly, ih, map_zero]
    ring

/-- A trailing zero does not change the polynomial. -/
private theorem toPoly_append_zero (l : List ℚ) : toPoly (l ++ [0]) = toPoly l := by
  induction l with
  | nil => simp [toPoly]
  | cons c l ih => simp [toPoly, ih]

/-- A list of zeros denotes zero. -/
private theorem toPoly_replicate (k : ℕ) : toPoly (List.replicate k 0) = 0 := by
  induction k with
  | zero => simp [toPoly]
  | succ k ih => simp [List.replicate_succ, toPoly, ih]

/-- Removing the trailing zeros of a list with one more entry. -/
private theorem trim_concat (l : List ℚ) (x : ℚ) :
    trim (l ++ [x]) = if x = 0 then trim l else l ++ [x] := by
  unfold QPoly.trim
  rw [List.rdropWhile_concat]
  simp only [decide_eq_true_eq]

/-- Removing the trailing zeros keeps the polynomial, leaves no trailing zero
and does not lengthen the list. -/
private theorem trim_spec (l : List ℚ) :
    toPoly (trim l) = toPoly l ∧ (trim l).getLast? ≠ some 0 ∧ (trim l).length ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [QPoly.trim]
  | append_singleton l x ih =>
    rw [trim_concat]
    split_ifs with hx
    · subst hx
      have := ih.2.2
      exact ⟨by rw [ih.1, toPoly_append_zero], ih.2.1, by simp; omega⟩
    · exact ⟨rfl, by simpa using hx, le_rfl⟩

/-- The tail of a list without trailing zeros has none. -/
private theorem getLast?_tail {c : ℚ} {l : List ℚ} (h : (c :: l).getLast? ≠ some 0) :
    l.getLast? ≠ some 0 := by
  cases l with
  | nil => simp
  | cons d l => simpa using h

/-- A list without trailing zeros denotes zero only when it is empty. -/
private theorem toPoly_eq_zero {l : List ℚ} (hl : l.getLast? ≠ some 0) (h : toPoly l = 0) :
    l = [] := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    exfalso
    have h0 : c = 0 := by simpa [toPoly] using congrArg (coeff · 0) h
    have ht : toPoly t = 0 := by simpa [toPoly, h0, X_ne_zero] using h
    have := ih (getLast?_tail hl) ht
    subst this
    subst h0
    exact hl rfl

/-- Lists without trailing zeros that denote the same polynomial are
equal. -/
private theorem toPoly_inj {l l' : List ℚ} (hl : l.getLast? ≠ some 0)
    (hl' : l'.getLast? ≠ some 0) (h : toPoly l = toPoly l') : l = l' := by
  induction l generalizing l' with
  | nil => exact (toPoly_eq_zero hl' (by simpa [toPoly] using h.symm)).symm
  | cons c t ih =>
    cases l' with
    | nil => exact toPoly_eq_zero hl (by simpa [toPoly] using h)
    | cons c' t' =>
      have hc : c = c' := by simpa [toPoly] using congrArg (coeff · 0) h
      subst hc
      have ht : toPoly t = toPoly t' := by simpa [toPoly, X_ne_zero] using h
      rw [ih (getLast?_tail hl) (getLast?_tail hl') ht]

/-- The degree of the polynomial of a list is below its length. -/
private theorem degree_toPoly_lt (l : List ℚ) : (toPoly l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_toPoly, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

/-- A list whose last entry is `1` denotes a monic polynomial of degree one
less than its length. -/
private theorem monic_toPoly {m : List ℚ} (h : m.getLast? = some 1) :
    (toPoly m).natDegree = m.length - 1 ∧ (toPoly m).Monic := by
  have hc : (toPoly m).coeff (m.length - 1) = 1 := by
    rw [coeff_toPoly, List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, h]
    rfl
  have hne : toPoly m ≠ 0 := fun h0 => by simp [h0] at hc
  have hnd : (toPoly m).natDegree = m.length - 1 := by
    apply le_antisymm
    · have := (natDegree_lt_iff_degree_lt hne).mpr (degree_toPoly_lt m)
      omega
    · exact le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero)
  exact ⟨hnd, by rw [Monic.def, leadingCoeff, hnd, hc]⟩

/-- Every polynomial of degree below `n` is denoted by a list of length
`n`. -/
private theorem exists_list (g : ℚ[X]) (n : ℕ) (hg : g.degree < n) :
    ∃ l : List ℚ, l.length = n ∧ toPoly l = g := by
  refine ⟨(List.range n).map g.coeff, by simp, ?_⟩
  ext i
  rw [coeff_toPoly, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < n
  · simp [hi]
  · simp [hi]
    exact (coeff_eq_zero_of_degree_lt (hg.trans_le (by exact_mod_cast not_lt.mp hi))).symm

/-- The last entry of a nonempty list. -/
private theorem getD_cons_length (c : ℚ) (r : List ℚ) :
    (c :: r).getD r.length 0 = r.getLastD c := by
  induction r generalizing c with
  | nil => rfl
  | cons d r ih => rw [List.length_cons, List.getD_cons_succ, ih, List.getLastD_cons]

/-- The sum is as long as the longer list. -/
private theorem length_add (p q : List ℚ) : (QPoly.add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [QPoly.add]
  | cons a p ih => cases q <;> simp [QPoly.add, ih]

/-- Dropping a last entry that is zero keeps the polynomial. -/
private theorem toPoly_dropLast (l : List ℚ) (h : (toPoly l).coeff (l.length - 1) = 0) :
    toPoly l.dropLast = toPoly l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x _ =>
    rw [coeff_toPoly] at h
    simp at h
    subst h
    rw [List.dropLast_concat, toPoly_append_zero]

/-- One step of the long division by `b` keeps the invariant `p = q b + r` with
a remainder of `b.length - 1` entries. -/
private theorem divStep_spec {b : List ℚ} (hb : b.getLast? ≠ some 0) (hb0 : b ≠ []) (c : ℚ)
    (qr : List ℚ × List ℚ) (hr : qr.2.length = b.length - 1) :
    (divStep b c qr).2.length = b.length - 1 ∧
      toPoly (divStep b c qr).1 * toPoly b + toPoly (divStep b c qr).2 =
        C c + X * (toPoly qr.1 * toPoly b + toPoly qr.2) := by
  have hlen : 0 < b.length := List.length_pos_iff.mpr hb0
  obtain ⟨z, hz⟩ : ∃ z, b.getLast? = some z := Option.ne_none_iff_exists'.mp (by simpa using hb0)
  have hz0 : z ≠ 0 := fun h => hb (h ▸ hz)
  have hbz : b.getLastD 0 = z := by rw [List.getLastD_eq_getLast?, hz]; rfl
  have hbD : b.getD (b.length - 1) 0 = z := by
    rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hz]
    rfl
  set t := qr.2.getLastD c / b.getLastD 0 with ht
  set s := QPoly.add (c :: qr.2) (scale (-t) b) with hs
  have hsl : s.length = b.length := by
    rw [hs, length_add]
    simp [scale]
    omega
  have hcoeff : (toPoly s).coeff (s.length - 1) = 0 := by
    rw [hs, toPoly_add, toPoly_scale, coeff_add, coeff_C_mul, coeff_toPoly, coeff_toPoly, ← hs,
      hsl, hbD, show b.length - 1 = qr.2.length by omega, getD_cons_length, ht, hbz]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · show s.dropLast.length = b.length - 1
    rw [List.length_dropLast, hsl]
  · show toPoly (t :: qr.1) * toPoly b + toPoly s.dropLast = _
    rw [toPoly_dropLast s hcoeff, hs, toPoly_add, toPoly_scale]
    simp only [toPoly, map_neg]
    ring

/-- The long division by a nonempty list `b` without trailing zeros, the list of
a nonzero polynomial: `p = q b + r`, and the remainder has no trailing zeros and
is shorter than `b`. -/
private theorem divMod_spec {b : List ℚ} (hb : b.getLast? ≠ some 0) (hb0 : b ≠ [])
    (p : List ℚ) :
    toPoly p = toPoly (divMod p b).1 * toPoly b + toPoly (divMod p b).2 ∧
      (divMod p b).2.getLast? ≠ some 0 ∧ (divMod p b).2.length < b.length := by
  have key : ∀ p : List ℚ,
      (p.foldr (divStep b) ([], List.replicate (b.length - 1) 0)).2.length = b.length - 1 ∧
      toPoly p = toPoly (p.foldr (divStep b) ([], List.replicate (b.length - 1) 0)).1 *
        toPoly b + toPoly (p.foldr (divStep b) ([], List.replicate (b.length - 1) 0)).2 := by
    intro p
    induction p with
    | nil => simp [toPoly_replicate, toPoly]
    | cons c p ih =>
      rw [List.foldr_cons]
      obtain ⟨hl', he'⟩ := divStep_spec hb hb0 c _ ih.1
      refine ⟨hl', ?_⟩
      rw [he', ← ih.2]
      rfl
  obtain ⟨hl, he⟩ := key p
  obtain ⟨t1, -, -⟩ := trim_spec (p.foldr (divStep b) ([], List.replicate (b.length - 1) 0)).1
  obtain ⟨t2, t2', t2''⟩ :=
    trim_spec (p.foldr (divStep b) ([], List.replicate (b.length - 1) 0)).2
  have hlen : 0 < b.length := List.length_pos_iff.mpr hb0
  refine ⟨?_, t2', ?_⟩
  · show toPoly p = toPoly (trim _) * toPoly b + toPoly (trim _)
    rw [t1, t2]
    exact he
  · show (trim _).length < b.length
    omega

/-- The extended Euclidean algorithm from a nonzero `r₀` and a remainder `r₁`
without trailing zeros, with their cofactors: when `r₁` is shorter than the
fuel, every common divisor of `r₀` and `r₁` divides `M` and `A`, and both
remainders are congruent modulo `M` to their cofactors times `A`, it ends with a
nonzero remainder that divides `M` and `A` and is congruent modulo `M` to its
cofactor times `A`. -/
private theorem euclid_spec (M A : ℚ[X]) :
    ∀ (fuel : ℕ) (r₀ s₀ r₁ s₁ : List ℚ), r₁.getLast? ≠ some 0 → r₁.length < fuel →
      toPoly r₀ ≠ 0 → (∀ d, d ∣ toPoly r₀ → d ∣ toPoly r₁ → d ∣ M ∧ d ∣ A) →
      M ∣ toPoly r₀ - toPoly s₀ * A → M ∣ toPoly r₁ - toPoly s₁ * A →
      toPoly (euclid fuel r₀ s₀ r₁ s₁).1 ∣ M ∧ toPoly (euclid fuel r₀ s₀ r₁ s₁).1 ∣ A ∧
        toPoly (euclid fuel r₀ s₀ r₁ s₁).1 ≠ 0 ∧
        M ∣ toPoly (euclid fuel r₀ s₀ r₁ s₁).1 - toPoly (euclid fuel r₀ s₀ r₁ s₁).2 * A := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro r₀ s₀ r₁ s₁ h1 hlen h0 hd c0 c1
    by_cases hr : r₁ = []
    · subst hr
      rw [euclid, ite_eq_left rfl]
      obtain ⟨dM, dA⟩ := hd _ dvd_rfl (by simp [toPoly])
      exact ⟨dM, dA, h0, c0⟩
    · rw [euclid, ite_eq_right hr]
      obtain ⟨e1, e2, e3⟩ := divMod_spec h1 hr r₀
      apply ih _ _ _ _ e2 (by omega) (fun hz => hr (toPoly_eq_zero h1 hz))
      · intro d d1 d2
        exact hd d (by rw [e1]; exact dvd_add (dvd_mul_of_dvd_right d1 _) d2) d1
      · exact c1
      · have hrem : toPoly (divMod r₀ r₁).2 = toPoly r₀ - toPoly (divMod r₀ r₁).1 * toPoly r₁ := by
          rw [e1]; ring
        rw [toPoly_sub, toPoly_mul, hrem]
        have := dvd_sub c0 (dvd_mul_of_dvd_right c1 (toPoly (divMod r₀ r₁).1))
        convert this using 1
        ring

/-- The first entry, `0` for the empty list. -/
private theorem headD_eq_getD (l : List ℚ) : l.headD 0 = l.getD 0 0 := by
  cases l <;> rfl

/-- `x² + c` over `ℚ`. -/
private theorem toPoly_quadratic (c : ℚ) : toPoly [c, 0, 1] = X ^ 2 - C (-c) := by
  simp [toPoly]
  ring

/-- `x² + c` is monic, and irreducible over `ℚ` when `-c` is not a square. -/
private theorem monicIrreducible_quadratic (c : ℚ) (hc : ∀ b : ℚ, b ^ 2 ≠ -c) :
    MonicIrreducible [c, 0, 1] :=
  ⟨rfl, by rw [toPoly_quadratic]; exact X_pow_sub_C_irreducible_of_prime Nat.prime_two hc⟩

end QPoly

/-- `x² + 1` is monic and irreducible over `ℚ`. -/
private theorem monicIrreducible_one : QPoly.MonicIrreducible [1, 0, 1] :=
  monicIrreducible_quadratic 1 fun b h => by nlinarith [sq_nonneg b]

/-- `x² - 2` is monic and irreducible over `ℚ`. -/
private theorem monicIrreducible_two : QPoly.MonicIrreducible [-2, 0, 1] := by
  refine monicIrreducible_quadratic (-2) fun b h => ?_
  have : ∃ q : ℚ, q * q = 2 := ⟨b, by rw [← sq, h]; norm_num⟩
  rw [Rat.exists_mul_self] at this
  revert this
  decide +kernel

/-! ## The number fields -/

section NumberFields

open QPoly

variable {Emb : Type}

/-- The minimal polynomial is not the empty list. -/
private theorem nf_minimal_ne (F : NumberField Emb) : F.minimal ≠ [] := fun h => by
  have := F.monicIrreducible.1
  rw [h] at this
  simp at this

/-- The minimal polynomial has no trailing zero. -/
private theorem nf_minimal_last (F : NumberField Emb) : F.minimal.getLast? ≠ some 0 := by
  rw [F.monicIrreducible.1]
  simp

/-- The empty list, zero, is canonical. -/
private theorem nf_nil_reduced (F : NumberField Emb) : NumberField.Reduced F.minimal [] :=
  ⟨by simp, List.length_pos_iff.mpr (nf_minimal_ne F)⟩

/-- The reduction of a list modulo the minimal polynomial is canonical and
denotes the class of the list. -/
private theorem nf_reduce (F : NumberField Emb) (p : List ℚ) :
    NumberField.Reduced F.minimal (NumberField.reduce F.minimal p) ∧
      (NumberField.model Emb F).interpret (NumberField.reduce F.minimal p) =
        AdjoinRoot.mk (toPoly F.minimal) (toPoly p) := by
  obtain ⟨h1, h2, h3⟩ := divMod_spec (nf_minimal_last F) (nf_minimal_ne F) p
  refine ⟨⟨h2, h3⟩, ?_⟩
  show AdjoinRoot.mk _ (toPoly (divMod p F.minimal).2) = _
  rw [AdjoinRoot.mk_eq_mk, h1]
  exact ⟨-(toPoly (divMod p F.minimal).1), by ring⟩

/-- A canonical element is of lower degree than the minimal polynomial. -/
private theorem nf_degree_lt (F : NumberField Emb) {e : List ℚ}
    (he : NumberField.Reduced F.minimal e) : (toPoly e).degree < (toPoly F.minimal).degree := by
  obtain ⟨hnd, hmon⟩ := monic_toPoly F.monicIrreducible.1
  have := he.2
  rw [degree_eq_natDegree hmon.ne_zero, hnd]
  exact (degree_toPoly_lt e).trans_le
    (by exact_mod_cast (by omega : e.length ≤ F.minimal.length - 1))

/-- Canonical elements are unique. -/
private theorem nf_unique (F : NumberField Emb) : (NumberField.model Emb F).Unique := by
  intro r s hr hs h
  change NumberField.Reduced F.minimal r at hr
  change NumberField.Reduced F.minimal s at hs
  change AdjoinRoot.mk _ (toPoly r) = AdjoinRoot.mk _ (toPoly s) at h
  rw [AdjoinRoot.mk_eq_mk] at h
  have h0 : toPoly r - toPoly s = 0 :=
    eq_zero_of_dvd_of_degree_lt h
      ((degree_sub_le _ _).trans_lt (max_lt (nf_degree_lt F hr) (nf_degree_lt F hs)))
  exact toPoly_inj hr.1 hs.1 (sub_eq_zero.mp h0)

/-- Every element of `Q(a)` has a canonical element: the remainder of a
polynomial that denotes it. -/
private theorem nf_complete (F : NumberField Emb) : (NumberField.model Emb F).Complete := by
  intro x
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨hnd, hmon⟩ := monic_toPoly F.monicIrreducible.1
  have hr : (g %ₘ toPoly F.minimal).degree < (F.minimal.length - 1 : ℕ) := by
    rw [← hnd, ← degree_eq_natDegree hmon.ne_zero]
    exact degree_modByMonic_lt g hmon
  obtain ⟨l, hl, hlg⟩ := exists_list _ _ hr
  obtain ⟨t1, t2, t3⟩ := trim_spec l
  have := List.length_pos_iff.mpr (nf_minimal_ne F)
  refine ⟨trim l, ⟨t2, by omega⟩, ?_⟩
  show AdjoinRoot.mk _ (toPoly (trim l)) = _
  rw [t1, hlg, AdjoinRoot.mk_eq_mk, modByMonic_eq_sub_mul_div g (toPoly F.minimal)]
  exact ⟨-(g /ₘ toPoly F.minimal), by ring⟩

/-- A canonical element is the empty list exactly when it denotes zero. -/
private theorem nf_eq_nil_iff (F : NumberField Emb) {a : List ℚ}
    (ha : NumberField.Reduced F.minimal a) :
    a = [] ↔ (NumberField.model Emb F).interpret a = 0 := by
  constructor
  · rintro rfl
    show AdjoinRoot.mk _ (toPoly []) = 0
    simp [toPoly]
  · intro h
    refine nf_unique F a [] ha (nf_nil_reduced F) ?_
    rw [h]
    show (0 : NumberField.Carrier F) = AdjoinRoot.mk _ (toPoly [])
    simp [toPoly]

/-- The rational `q` as an element is canonical and denotes its image. -/
private theorem nf_ofRat (F : NumberField Emb) (q : ℚ) :
    (NumberField.model Emb F).canonical (NumberField.ofRat F.minimal q) ∧
      (NumberField.model Emb F).interpret (NumberField.ofRat F.minimal q) =
        AdjoinRoot.of (toPoly F.minimal) q :=
  ⟨(nf_reduce F [q]).1, (nf_reduce F [q]).2.trans (by simp [toPoly])⟩

/-- The reduction of a list is a canonical value that denotes its class. -/
private theorem nf_reduce_yields (F : NumberField Emb) (p : List ℚ) (x : NumberField.Carrier F)
    (hx : AdjoinRoot.mk (toPoly F.minimal) (toPoly p) = x) :
    (NumberField.model Emb).Yields F (.value (NumberField.reduce F.minimal p)) x :=
  ⟨_, rfl, (nf_reduce F p).1, (nf_reduce F p).2.trans hx⟩

/-- The ring laws of the number fields. -/
private theorem nf_ringLaws [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage) :
    RingLaws (NumberField.field Emb μ).toCoefficientRing (NumberField.model Emb) where
  unique := nf_unique
  zero F := ⟨nf_nil_reduced F, by simp [NumberField.field, NumberField.model, toPoly]⟩
  one F := ⟨(nf_ofRat F 1).1, (nf_ofRat F 1).2.trans (map_one _)⟩
  fromInteger F n := ⟨(nf_ofRat F n).1, (nf_ofRat F n).2.trans (map_intCast _ n)⟩
  negate F a _ := nf_reduce_yields F _ _ (by rw [toPoly_scale]; simp [NumberField.model])
  add F a b _ _ := nf_reduce_yields F _ _ (by rw [toPoly_add, map_add]; rfl)
  subtract F a b _ _ := nf_reduce_yields F _ _ (by rw [toPoly_sub, map_sub]; rfl)
  multiply F a b _ _ := nf_reduce_yields F _ _ (by rw [toPoly_mul, map_mul]; rfl)

/-- The inverse of a nonzero canonical element: the extended Euclidean
algorithm ends with a nonzero constant `g`, since the minimal polynomial is
irreducible and does not divide the element, and the cofactor divided by `g`
is the inverse. -/
private theorem nf_inverse (F : NumberField Emb) {a : List ℚ}
    (ha : NumberField.Reduced F.minimal a) (h0 : a ≠ []) :
    ∃ b, NumberField.inverse F.minimal a = .value b ∧ NumberField.Reduced F.minimal b ∧
      (NumberField.model Emb F).interpret a * (NumberField.model Emb F).interpret b = 1 := by
  have hirr : Irreducible (toPoly F.minimal) := F.monicIrreducible.2
  have hA : toPoly a ≠ 0 := fun hz => h0 (toPoly_eq_zero ha.1 hz)
  have hMA : ¬toPoly F.minimal ∣ toPoly a := fun hd =>
    hA (eq_zero_of_dvd_of_degree_lt hd (nf_degree_lt F ha))
  obtain ⟨gM, gA, g0, gc⟩ := euclid_spec (toPoly F.minimal) (toPoly a) F.minimal.length
    F.minimal [] a [1] ha.1 ha.2 hirr.ne_zero (fun d d1 d2 => ⟨d1, d2⟩) (by simp [toPoly])
    (by simp [toPoly])
  have hinv : NumberField.inverse F.minimal a = .value (NumberField.reduce F.minimal
      (scale ((euclid F.minimal.length F.minimal [] a [1]).1.headD 0)⁻¹
        (euclid F.minimal.length F.minimal [] a [1]).2)) := by
    rw [NumberField.inverse, ite_eq_right h0]
  generalize euclid F.minimal.length F.minimal [] a [1] = rs at gM gA g0 gc hinv
  have hu : IsUnit (toPoly rs.1) := by
    obtain ⟨k, hk⟩ := gM
    rcases hirr.isUnit_or_isUnit hk with h | h
    · exact h
    · refine absurd ?_ hMA
      have : toPoly F.minimal ∣ toPoly rs.1 := by
        rw [hk]
        exact h.mul_right_dvd.mpr dvd_rfl
      exact this.trans gA
  obtain ⟨g, hg, hgC⟩ := Polynomial.isUnit_iff.mp hu
  have hg0 : g ≠ 0 := hg.ne_zero
  have hhead : rs.1.headD 0 = g := by
    have := congrArg (coeff · 0) hgC
    simp only [coeff_C_zero, coeff_toPoly] at this
    rw [headD_eq_getD, this]
  refine ⟨NumberField.reduce F.minimal (scale g⁻¹ rs.2), by rw [hinv, hhead], (nf_reduce F _).1, ?_⟩
  · have hSA : AdjoinRoot.mk (toPoly F.minimal) (toPoly rs.2) *
        AdjoinRoot.mk (toPoly F.minimal) (toPoly a) = AdjoinRoot.mk (toPoly F.minimal) (C g) := by
      rw [← map_mul, hgC, AdjoinRoot.mk_eq_mk, ← neg_sub, dvd_neg]
      exact gc
    rw [(nf_reduce F _).2, toPoly_scale, map_mul]
    show AdjoinRoot.mk _ (toPoly a) * _ = _
    calc AdjoinRoot.mk (toPoly F.minimal) (toPoly a) *
          (AdjoinRoot.mk (toPoly F.minimal) (C g⁻¹) *
            AdjoinRoot.mk (toPoly F.minimal) (toPoly rs.2))
        = AdjoinRoot.mk (toPoly F.minimal) (C g⁻¹) *
          (AdjoinRoot.mk (toPoly F.minimal) (toPoly rs.2) *
            AdjoinRoot.mk (toPoly F.minimal) (toPoly a)) := by ring
      _ = AdjoinRoot.mk (toPoly F.minimal) (C g⁻¹ * C g) := by rw [hSA, map_mul]
      _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hg0, C_1, map_one]

/-- The field laws of the number fields. -/
private theorem nf_fieldLaws [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage) :
    FieldLaws (NumberField.field Emb μ) (NumberField.model Emb) where
  inverse F a ha h := nf_inverse F ha fun hn => h ((nf_eq_nil_iff F ha).mp hn)
  inverse_zero F a ha h := by
    obtain rfl := (nf_eq_nil_iff F ha).mpr h
    rfl
  divide F a b ha hb h := by
    obtain ⟨c, hc, hcr, hcm⟩ := nf_inverse F hb fun hn => h ((nf_eq_nil_iff F hb).mp hn)
    refine ⟨NumberField.multiply F.minimal a c, ?_, (nf_reduce F _).1, ?_⟩
    · show (NumberField.inverse F.minimal b).map (NumberField.multiply F.minimal a) = _
      rw [hc]
      rfl
    · show (NumberField.model Emb F).interpret (NumberField.reduce F.minimal (QPoly.mul a c)) *
        _ = _
      rw [(nf_reduce F _).2, toPoly_mul, map_mul, mul_assoc,
        mul_comm _ ((NumberField.model Emb F).interpret b)]
      show AdjoinRoot.mk _ (toPoly a) * ((NumberField.model Emb F).interpret b *
        (NumberField.model Emb F).interpret c) = _
      rw [hcm, mul_one]
      rfl
  divide_zero F a b ha hb h := by
    obtain rfl := (nf_eq_nil_iff F hb).mpr h
    rfl

/-- The zero test of the number fields is exact. -/
private theorem nf_zeroTestExact [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage) :
    ZeroTestExact (NumberField.field Emb μ).toCoefficientRing (NumberField.model Emb) :=
  ⟨fun F _ ha => (ofDecide_exact _ _ (nf_eq_nil_iff F ha)).1,
    fun F _ ha => (ofDecide_exact _ _ (nf_eq_nil_iff F ha)).2⟩

/-- Two number fields are the same exactly when their minimal polynomials and
their embeddings are equal. -/
private theorem nf_sameParent_iff [DecidableEq Emb] (μ : NumberField Emb → List ℚ → Storage)
    (F G : NumberField Emb) :
    (NumberField.field Emb μ).sameParent F G = true ↔
      F.minimal = G.minimal ∧ F.embedding = G.embedding := by
  show decide (F = G) = true ↔ _
  rw [decide_eq_true_iff]
  cases F
  cases G
  simp

end NumberFields

/-! ## The properties -/

/-- Proves `RingAxioms`. -/
public theorem ringAxioms : RingAxioms :=
  ⟨rat_ringLaws, int_ringLaws, residue_ringLaws, prime_ringLaws, fun _ _ μ => nf_ringLaws μ⟩

/-- Proves `FieldAxioms`. -/
public theorem fieldAxioms : FieldAxioms :=
  ⟨rat_fieldLaws, prime_fieldLaws, fun _ _ μ => nf_fieldLaws μ⟩

/-- Proves `RingDivisionAndInverse`. -/
public theorem ringDivisionAndInverse : RingDivisionAndInverse := by
  refine ⟨int_exactDivisionLaws, fun μ => ⟨residue_unitInverseLaws μ, ?_, ?_, ?_, ?_⟩⟩
  · intro R a _
    exact (ZMod.isUnit_iff_coprime a R.modulus).trans Nat.coprime_iff_gcd_eq_one
  · intro R a ha h0 hg
    have hv : (a : ZMod R.modulus).val = a := ZMod.val_cast_of_lt ha
    have hx : (a : ZMod R.modulus) ≠ 0 := by
      intro h
      apply h0
      rw [← hv, h, ZMod.val_zero]
    have hu : ¬IsUnit (a : ZMod R.modulus) := fun hu =>
      hg (((ZMod.isUnit_iff_coprime a _).trans Nat.coprime_iff_gcd_eq_one).mp hu)
    have hpos : 0 < Nat.gcd a R.modulus := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h0)
    refine ⟨?_, by omega, lt_of_le_of_lt (Nat.gcd_le_left _ (Nat.pos_of_ne_zero h0)) ha⟩
    rw [residue_unitInverse μ R ha, residueInverseOp_nonUnit _ _ hx hu, hv]
    rfl
  · intro R hR
    have hR' : 1 < (R.modulus : ℕ) := by exact_mod_cast hR
    rw [residue_unitInverse μ R R.modulus.pos,
      show ((0 : ℕ) : ZMod R.modulus) = 0 from Nat.cast_zero, residueInverseOp_zero _ hR']
    rfl
  · dsimp only [ResidueRing.ring]
    decide +kernel

/-- Proves `ZeroTestsAreExact`. -/
public theorem zeroTestsAreExact : ZeroTestsAreExact :=
  ⟨rat_zeroTestExact, int_zeroTestExact, residue_zeroTestExact, prime_zeroTestExact,
    fun _ _ μ => nf_zeroTestExact μ⟩

/-- Proves `CanonicalFormsAreUniqueAndComplete`. -/
public theorem canonicalFormsAreUniqueAndComplete : CanonicalFormsAreUniqueAndComplete :=
  ⟨fun p => ⟨rat_unique p, rat_complete p⟩,
    fun _ => ⟨fun _ _ _ _ h => h, fun x => ⟨x, trivial, rfl⟩⟩,
    fun R => ⟨residue_unique R, fun x => ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩⟩,
    fun F => ⟨prime_unique F, fun x => ⟨F.ofZMod x, prime_ofZMod F x⟩⟩,
    fun _ F => ⟨nf_unique F, nf_complete F⟩⟩

/-- Proves `MapsPreserveOperations`. -/
public theorem mapsPreserveOperations : MapsPreserveOperations := by
  refine ⟨?_, ?_, ?_, toPrimeField_partialOn, ?_⟩
  · intro n _
    rw [ofRingHom_apply]
    exact ⟨⟨n, 1⟩, rfl, int_fraction n⟩
  · intro F n _
    rw [intResidues, ofRingHom_apply]
    exact ⟨_, rfl, prime_ringLaws.fromInteger F n⟩
  · intro R n _
    rw [intResidues, ofRingHom_apply]
    exact ⟨_, rfl, (residue_ringLaws fun _ _ => ⟨0, 0⟩).fromInteger R n⟩
  · intro Emb F x _
    rw [ofRingHom_apply]
    exact ⟨_, rfl, nf_ofRat F _⟩

/-- Proves `ParallelPathsCommute`. -/
public theorem parallelPathsCommute : ParallelPathsCommute := by
  refine ⟨fun _ _ f g => RingHom.ext_int f g, fun F n => ?_, fun Emb _ μ F n => ?_⟩
  · have : NeZero F.modulus := ⟨F.prime.ne_zero⟩
    have h1 : Fraction.interpret ⟨n, 1⟩ = n := (int_fraction n).2
    have hd : ¬F.modulus ∣ (n : ℚ).den := by simpa using F.prime.ne_one
    show (ratReduceOp F.modulus (Fraction.interpret ⟨n, 1⟩)).map (MapResult.map F.ofZMod) =
      .value (.mapped ⟨(n % (F.modulus : ℤ)).toNat⟩)
    rw [h1, ratReduceOp, ratReduce, ite_eq_right hd, Rat.num_intCast, Rat.den_intCast,
      Nat.cast_one, ZMod.inv_eq_of_mul_eq_one _ 1 1 (mul_one 1), mul_one]
    show Outcome.value (MapResult.mapped (PrimeResidue.mk (n : ZMod F.modulus).val)) = _
    rw [← Int.toNat_natCast (n : ZMod F.modulus).val, ZMod.val_intCast]
  · show Outcome.value
        (MapResult.mapped (NumberField.ofRat F.minimal (Fraction.interpret ⟨n, 1⟩))) =
      .value (.mapped (NumberField.ofRat F.minimal n))
    rw [(int_fraction n).2]

/-- Proves `ReductionOutsideItsDomain`. -/
public theorem reductionOutsideItsDomain : ReductionOutsideItsDomain := by
  intro F a
  by_cases h : F.modulus ∣ a.interpret.den
  · have e : Rationals.toPrimeField.apply ⟨⟩ F a = .value .notInDomain := by
      show (ratReduceOp _ _).map _ = _
      rw [ratReduceOp, ratReduce, ite_eq_left h]
      rfl
    exact ⟨⟨_, e⟩, iff_of_true e h, fun h' => absurd h h'⟩
  · have e : Rationals.toPrimeField.apply ⟨⟩ F a = .value (.mapped (F.ofZMod
        ((a.interpret.num : ZMod F.modulus) * (a.interpret.den : ZMod F.modulus)⁻¹))) := by
      show (ratReduceOp _ _).map _ = _
      rw [ratReduceOp, ratReduce, ite_eq_right h]
      rfl
    refine ⟨⟨_, e⟩, iff_of_false (by rw [e]; simp) h, fun _ => ⟨_, e, prime_ofZMod F _⟩⟩

/-! ## The examples -/

/-- Proves `CanonicalFormExamples`. -/
public theorem canonicalFormExamples : CanonicalFormExamples := by
  refine ⟨by decide +kernel, ⟨by decide, by decide⟩, by decide +kernel, monicIrreducible_one, ?_⟩
  intro Emb _ μ F hF
  dsimp only [NumberField.field, NumberField.model]
  rw [hF]
  unfold NumberField.Reduced
  decide +kernel

/-- Proves `NonCanonicalRepresentatives`. -/
public theorem nonCanonicalRepresentatives : NonCanonicalRepresentatives :=
  ⟨fun h => absurd h.2 (by decide), fun h => absurd h.1 (by decide), seven, new_seven,
    fun h => lt_irrefl 7 h, by decide +kernel⟩

/-- Proves `InverseExamples`. -/
public theorem inverseExamples : InverseExamples := by
  refine ⟨by decide +kernel, ⟨seven, new_seven, by decide +kernel⟩, monicIrreducible_one, ?_⟩
  intro Emb _ μ F hF
  dsimp only [NumberField.field]
  rw [hF]
  decide +kernel

/-- Proves `ZeroHasNoInverse`. -/
public theorem zeroHasNoInverse : ZeroHasNoInverse := by
  refine ⟨by decide +kernel, by decide +kernel, fun m o => ?_, fun m o => ?_,
    ⟨seven, new_seven, by decide +kernel, by decide +kernel, fun m o => ?_, fun m o => ?_⟩,
    monicIrreducible_one, ?_⟩
  · rw [RatUnary.Admits, show RatUnary.exact .inv 0 = .fault .divisionByZero by decide +kernel]
    exact admits_fault _ _ _ _
  · rw [RatOp.Admits, show RatOp.exact .div 1 0 = .fault .divisionByZero by decide +kernel]
    exact admits_fault _ _ _ _
  · rw [PrimeMethod.Admits,
      show PrimeMethod.domain seven (.inverse ⟨0⟩) = .fault .divisionByZero by decide +kernel]
    exact admits_fault _ _ _ _
  · rw [PrimeMethod.Admits,
      show PrimeMethod.domain seven (.divide ⟨1⟩ ⟨0⟩) = .fault .divisionByZero by decide +kernel]
    exact admits_fault _ _ _ _
  · intro Emb _ μ F _
    exact ⟨rfl, rfl⟩

/-- Proves `PowerExamples`. -/
public theorem powerExamples : PowerExamples := by
  refine ⟨fun a => by simp [ratPowOp, ratPow, FieldError.lift], by decide +kernel,
    by decide +kernel, fun o => ?_⟩
  rw [ratPowAdmits, show checkLimit .exponent 0 (0 : ℤ).natAbs (ratPowOp 0 0) = .value 1 by
    decide +kernel]
  apply admits_value
  · show ¬1 < max (ratPowEstimate 0 0) (ratBits 0)
    decide +kernel
  · show ¬1 < ratBits 1
    decide +kernel

/-- Proves `PowerFailures`. -/
public theorem powerFailures : PowerFailures := by
  refine ⟨by decide +kernel, fun me mb o h1 => ?_, fun mb o => ?_, fun me => ?_⟩
  · have hc : checkLimit .exponent me (-1 : ℤ).natAbs (ratPowOp 0 (-1)) =
        .fault .divisionByZero := by
      rw [checkLimit, ite_eq_right (by simp; omega)]
      decide +kernel
    rw [ratPowAdmits, hc]
    exact admits_fault _ _ _ _
  · rw [ratPowAdmits, show checkLimit .exponent 2 (-3 : ℤ).natAbs (ratPowOp 0 (-3)) =
      .resourceLimit .exponent by decide +kernel]
    exact admits_limit _ _ _ _
  · have hc : checkLimit .exponent me (0 : ℤ).natAbs (ratPowOp 16 0) = .value 1 := by
      rw [checkLimit, ite_eq_right (by simp)]
      decide +kernel
    rw [ratPowAdmits, hc]
    exact Or.inr ⟨rfl, 1, rfl, Or.inl (by
      show 3 < max (ratPowEstimate 16 0) (ratBits 16)
      decide +kernel)⟩

/-- Proves `ZeroTestExamples`. -/
public theorem zeroTestExamples : ZeroTestExamples := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fun μ => ?_,
    ⟨seven, new_seven, by decide +kernel, by decide +kernel⟩, monicIrreducible_one, ?_⟩
  · dsimp only [ResidueRing.ring]
    decide +kernel
  · intro Emb _ μ F hF
    dsimp only [NumberField.field]
    rw [hF]
    decide +kernel

/-- Proves `ZeroTestsOfHiddenZeros`. -/
public theorem zeroTestsOfHiddenZeros : ZeroTestsOfHiddenZeros := by
  refine ⟨⟨seven, new_seven, by decide +kernel⟩, monicIrreducible_one, ?_⟩
  intro Emb _ μ F hF
  dsimp only [NumberField.field]
  rw [hF]
  decide +kernel

/-- Proves `EqualNumberFieldsCombine`. -/
public theorem equalNumberFieldsCombine : EqualNumberFieldsCombine := by
  refine ⟨fun _ _ μ F G => nf_sameParent_iff μ F G, monicIrreducible_one, ?_⟩
  intro Emb _ μ F G hF hG he
  have hs : (NumberField.field Emb μ).sameParent F G = true :=
    (nf_sameParent_iff μ F G).mpr ⟨hF.trans hG.symm, he⟩
  have hc : NumberField.add [1, 0, 1] (NumberField.generator [1, 0, 1])
      (NumberField.ofRat [1, 0, 1] 1) = [1, 1] := by decide +kernel
  dsimp only
  refine ⟨hs, ?_⟩
  rw [CoefficientRing.paired, CoefficientRing.requireSameParent, ite_eq_left hs]
  dsimp only [NumberField.field]
  rw [hF, hG, hc]
  rfl

/-- Proves `DifferentNumberFieldsMismatch`. -/
public theorem differentNumberFieldsMismatch : DifferentNumberFieldsMismatch := by
  refine ⟨monicIrreducible_one, monicIrreducible_two, ?_, ?_⟩
  · intro Emb _ μ F G hF hG
    have hs : ¬(NumberField.field Emb μ).sameParent F G = true := by
      rw [nf_sameParent_iff, hF, hG]
      intro h
      exact absurd h.1 (by decide +kernel)
    dsimp only
    rw [CoefficientRing.paired, CoefficientRing.requireSameParent, ite_eq_right hs,
      CoefficientRing.paired, CoefficientRing.requireSameParent, ite_eq_right hs]
    exact ⟨rfl, rfl⟩
  · intro Emb _ μ F G _ he
    have hs : ¬(NumberField.field Emb μ).sameParent F G = true := by
      rw [nf_sameParent_iff]
      exact fun h => he h.2
    dsimp only
    rw [CoefficientRing.paired, CoefficientRing.requireSameParent, ite_eq_right hs]

/-- Proves `MapExamples`. -/
public theorem mapExamples : MapExamples := by
  refine ⟨⟨seven, new_seven, by decide +kernel⟩, monicIrreducible_one, ?_⟩
  intro Emb F hF
  show Outcome.value (MapResult.mapped (NumberField.ofRat F.minimal (Fraction.interpret ⟨1, 2⟩))) =
    _
  rw [hF]
  decide +kernel

/-- Proves `ReductionOfOneSeventh`. -/
public theorem reductionOfOneSeventh : ReductionOfOneSeventh :=
  ⟨seven, new_seven, by decide +kernel⟩

/-- Proves `ProductWithinBitLimit`. -/
public theorem productWithinBitLimit : ProductWithinBitLimit := by
  refine ⟨fun o => ?_, by decide +kernel⟩
  rw [RatOp.Admits, show RatOp.exact .mul (1 / 2) (1 / 2) = .value (1 / 4) by decide +kernel]
  apply admits_value
  · show ¬4 < RatOp.estimate .mul (1 / 2) (1 / 2)
    decide +kernel
  · show ¬4 < ratBits (1 / 4)
    decide +kernel

/-- Proves `ProductBeyondBitLimit`. -/
public theorem productBeyondBitLimit : ProductBeyondBitLimit := by
  refine ⟨Or.inr ⟨rfl, _, rfl, Or.inl ?_⟩, fun o => ?_⟩
  · show 3 < RatOp.estimate .mul (1 / 2) (1 / 2)
    decide +kernel
  · rw [RatOp.Admits, show RatOp.exact .div 1 0 = .fault .divisionByZero by decide +kernel]
    exact admits_fault _ _ _ _

/-- Proves `IntegerDivisionExamples`. -/
public theorem integerDivisionExamples : IntegerDivisionExamples := by
  refine ⟨by decide +kernel, fun u => ?_⟩
  by_cases h0 : u = 0
  · subst h0
    simp [Integers.ring, exactDivOp, exactDiv, FieldError.lift]
  · by_cases hd : u ∣ 1
    · have : u = 1 ∨ u = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hd)
      simp [Integers.ring, exactDivOp, exactDiv, FieldError.lift, h0, hd, this]
    · have : ¬(u = 1 ∨ u = -1) := fun h => hd (by rcases h with rfl | rfl <;> decide)
      simp only [this, iff_false]
      simp [Integers.ring, exactDivOp, exactDiv, FieldError.lift, h0, hd]

/-- Proves `IntegerDivisionFailures`. -/
public theorem integerDivisionFailures : IntegerDivisionFailures :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Proves `ResidueInverseExamples`. -/
public theorem residueInverseExamples : ResidueInverseExamples := by
  intro μ
  dsimp only [ResidueRing.ring]
  decide +kernel

/-- Proves `ResidueFailures`. -/
public theorem residueFailures : ResidueFailures :=
  ⟨fun μ => by dsimp only [ResidueRing.ring]; decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- Proves `IntegerPathsAndResiduesAgree`. -/
public theorem integerPathsAndResiduesAgree : IntegerPathsAndResiduesAgree := by
  refine ⟨⟨seven, new_seven, by decide +kernel, by decide +kernel, by decide +kernel⟩,
    fun μ => by dsimp only [ResidueRing.ring]; decide +kernel, ?_⟩
  intro μ R F hRF a b ha hb
  obtain ⟨n⟩ := R
  obtain ⟨p, hp, hw⟩ := F
  dsimp only at hRF ha hb
  subst hRF
  have hr : ∀ op : ResidueOp, (⟨n⟩ : ResidueRing).op op a b =
      .value (op.value (a : ZMod n) b).val := fun op => residue_op ⟨n⟩ op ha hb
  refine ⟨?_, ?_, ?_, fun h0 => ?_⟩
  · show (⟨n⟩ : ResidueRing).op .add a b = _
    rw [hr]
    show _ = (PrimeField.binary ⟨n, hp, hw⟩ (fun x y => .value (x + y)) ⟨a⟩ ⟨b⟩).map _
    rw [prime_binary _ _ ha hb]
    rfl
  · show (⟨n⟩ : ResidueRing).op .sub a b = _
    rw [hr]
    show _ = (PrimeField.binary ⟨n, hp, hw⟩ (fun x y => .value (x - y)) ⟨a⟩ ⟨b⟩).map _
    rw [prime_binary _ _ ha hb]
    rfl
  · show (⟨n⟩ : ResidueRing).op .mul a b = _
    rw [hr]
    show _ = (PrimeField.binary ⟨n, hp, hw⟩ (fun x y => .value (x * y)) ⟨a⟩ ⟨b⟩).map _
    rw [prime_binary _ _ ha hb]
    rfl
  · have hx : (a : ZMod n) ≠ 0 := by
      intro h
      apply h0
      rw [← ZMod.val_cast_of_lt ha, h, ZMod.val_zero]
    have hu : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).mpr
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd =>
        h0 (Nat.eq_zero_of_dvd_of_lt hd ha)))
    rw [residue_unitInverse μ ⟨n⟩ ha, (residueInverseOp_unit _ _ hu).1]
    show _ = (PrimeField.unary ⟨n, hp, hw⟩ (primeInverseOp n) ⟨a⟩).map _
    rw [prime_unary _ _ ha, primeInverseOp, primeInverse,
      ite_eq_right (show ¬PrimeField.toZMod ⟨n, hp, hw⟩ ⟨a⟩ = 0 from hx)]
    rfl

/-- Proves `ResidueRingsAndPrimeFieldsDiffer`. -/
public theorem residueRingsAndPrimeFieldsDiffer : ResidueRingsAndPrimeFieldsDiffer := by
  refine ⟨fun μ R S => decide_eq_true_iff, fun F G => ?_,
    fun μ => by dsimp only [ResidueRing.ring]; decide +kernel, seven, new_seven,
    by decide +kernel⟩
  show decide (F.modulus = G.modulus) = true ↔ F = G
  rw [decide_eq_true_iff]
  obtain ⟨m, _, _⟩ := F
  obtain ⟨m', _, _⟩ := G
  constructor
  · rintro (rfl : m = m')
    rfl
  · rintro ⟨⟩
    rfl

end Kalyx.Proofs.Fields
