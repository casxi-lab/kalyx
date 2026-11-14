module

public meta import Kalyx.Spec.Terms.Power
public meta import Kalyx.Spec.Terms.Call
public meta import Kalyx.Spec.Terms.Eval

/-!
# Replays of the vectors of the term core

The vectors whose answers only the term core decides, replayed through the
specification of `Kalyx.Spec.Terms` with `#guard`: the evaluations and the
error cases of `vectors/r02.tsv` and `vectors/cli_cases.tsv`, and the rows of
`vectors/library.tsv` and `vectors/root_calls.tsv` that read an input into its
canonical term, without assumptions. Each input is written as an input tree
`E`, unnormalized, and `E.canon` builds its canonical term through the
constructors, an operator at a time, as a parse builds it. The answer is read
back the same way, so an answer is compared with the input by canonical form,
the two terms by structure, as the vectors compare them; an error is compared
by its kind.

The parser is not part of the replay: an input tree is written in Lean, whose
operators have the precedence of kalyx's grammar, so `-2^2` is the negation of
`2²`; the exponent `3^2` of `2^3^2` is written as a natural number; and the
decimal literals `0.1` and `0.2` are replayed from the rationals `1/10` and
`1/5` that the parser reads. The rows of `eval` read the canonical term with
`Term.eval`; the other rows compare canonical terms. Every call is of a
function of the registry, built under the rules that keep every call
(`RegistryRules.empty`), so the rule of the powers of roots is the only rule
that applies to a call. The order is `Orders.sample`, which no input reads,
and the limit `defaultMaxExponent`, or the `max_exponent` that a row's limits
set.
-/

namespace Kalyx.SpecTests.Terms

open Kalyx.Spec.Terms

/-! ## Input trees -/

/-- An input tree, as the input text writes a term: numbers, symbols, the
constant `i`, the operators, integer powers and calls of registry functions of
one or two arguments. -/
inductive E where
  | num (q : ℚ)
  | sym (name : String)
  | const (c : NamedConstant)
  | add (a b : E)
  | sub (a b : E)
  | mul (a b : E)
  | div (a b : E)
  | neg (a : E)
  | pow (a : E) (k : ℤ)
  | call1 (name : String) (a : E)
  | call2 (name : String) (a b : E)

meta instance (n : ℕ) : OfNat E n := ⟨.num n⟩
meta instance : Add E := ⟨.add⟩
meta instance : Sub E := ⟨.sub⟩
meta instance : Mul E := ⟨.mul⟩
meta instance : Div E := ⟨.div⟩
meta instance : Neg E := ⟨.neg⟩
meta instance : HPow E ℕ E := ⟨fun a k => .pow a k⟩
meta instance : HPow E ℤ E := ⟨fun a k => .pow a k⟩

/-- The symbol `x`. -/
meta def x : E := .sym "x"

/-- The symbol `y`. -/
meta def y : E := .sym "y"

/-- The constant `i`. -/
meta def iu : E := .const .i

/-- A rational number. -/
meta def q (r : ℚ) : E := .num r

/-- The natural number of the decimal digits `digits`, joined. -/
meta def big (digits : List String) : E := .num (String.join digits).toNat!

/-- A call of the registry function `name` of one argument. -/
meta def fn (name : String) (a : E) : E := .call1 name a

/-- A call of the registry function `name` of two arguments. -/
meta def fn2 (name : String) (a b : E) : E := .call2 name a b

/-- The canonical term of an input tree under `maxExponent`, built through the
constructors: the sum, the difference, the product, the quotient, the
negation and the power of the canonical terms of the operands, the symbol
constructor, and the call constructor under the rules that keep every call.
The first error in the order of the input is the result. -/
meta def E.canonAt (maxExponent : ℕ) : E → Result Term
  | .num r => .value (.number r)
  | .sym name => mkSymbol name
  | .const c => .value (.constant (.named c))
  | .add a b => do mkSum Orders.sample [← a.canonAt maxExponent, ← b.canonAt maxExponent]
  | .sub a b => do
    mkSubtract Orders.sample maxExponent (← a.canonAt maxExponent) (← b.canonAt maxExponent)
  | .mul a b => do
    mkProduct Orders.sample maxExponent [← a.canonAt maxExponent, ← b.canonAt maxExponent]
  | .div a b => do
    mkDivide Orders.sample maxExponent (← a.canonAt maxExponent) (← b.canonAt maxExponent)
  | .neg a => do mkNegate Orders.sample maxExponent (← a.canonAt maxExponent)
  | .pow a k => do mkPower Orders.sample maxExponent (← a.canonAt maxExponent) k
  | .call1 name a => do
    mkCall maxExponent RegistryRules.empty ⟨name, .registered⟩ [← a.canonAt maxExponent]
  | .call2 name a b => do
    mkCall maxExponent RegistryRules.empty ⟨name, .registered⟩
      [← a.canonAt maxExponent, ← b.canonAt maxExponent]

/-- The canonical term of an input tree under the default limit. -/
meta def E.canon (e : E) : Result Term := e.canonAt defaultMaxExponent

/-- The input and the answer have the same canonical term. -/
meta def same (input answer : E) : Bool := input.canon == answer.canon

/-- `eval` of the canonical term of an input. -/
meta def evalOf (input : E) : Result EvalAnswer := input.canon.bind (Term.eval .asIs)

/-- `eval` of the input gives the canonical term of the answer as its value. -/
meta def evals (input answer : E) : Bool := evalOf input == answer.canon.map EvalAnswer.value

/-- The sum of `n` numbers that run through 1 to 7 in turn, added from the
left: `1+2+3+…`. -/
meta def flatSum (n : ℕ) : E :=
  match (List.range n).map fun k => E.num ((k % 7 + 1 : ℕ) : ℚ) with
  | [] => 0
  | a :: rest => rest.foldl .add a

/-- The balanced sum of depth `d` whose leaves, from the leaf `k` on, run
through 1 to 7 in turn. -/
meta def balanced : ℕ → ℕ → E
  | 0, k => .num ((k % 7 + 1 : ℕ) : ℚ)
  | d + 1, k => .add (balanced d (2 * k)) (balanced d (2 * k + 1))

/-- The balanced sum of `2 ^ d` numbers that run through 1 to 7 in turn:
`((1+2)+(3+4))+…`. -/
meta def balancedSum (d : ℕ) : E := balanced d 0

/-- `1+(1+(…+(1)))` with `n` additions, nested to the right. -/
meta def rightNested : ℕ → E
  | 0 => 1
  | n + 1 => .add 1 (rightNested n)

/-! ## Wide numbers

The operands and the answers of the products and the sums of fractions of
`vectors/r02.tsv` from 64 bits up: `aN * bN` is `pN`, and `aN/bN + bN/aN` is
`sN/pN`.
-/

meta def a64 : E := 10001292739316180759
meta def b64 : E := 16453378065995171361
meta def p64 : E := 164555050588661611706850353150256042999
meta def s64 : E := 370739506240069560289473947042116408402
meta def a128 : E := 239992932708435402801661488948312043561
meta def b128 : E := 240440942432219566272722861453719830081
meta def p128 : E := big [
  "577041269174884608795396412427385844307738172565466982768221",
  "47817262790158441"]
meta def s128 : E := big [
  "115408454547689526921527811245850810998424104019893717004269",
  "937189571474027282"]
meta def a256 : E := big [
  "718031949919271345003672457129996029405214503280729680874872",
  "27924493550393429"]
meta def b256 : E := big [
  "778218226756888815072281690840845680657504717967738712737821",
  "50748493136464015"]
meta def p256 : E := big [
  "558785550820966541079829140473966738165174416869250818318747",
  "886465545656294114782162405171021479238432643128460748076988",
  "4895057771672303485580789150957435"]
meta def s256 : E := big [
  "112119348956150741133320341566461036446364542254004610592044",
  "844898482059407048648201840397390326103571333023227980352882",
  "01511902938873180052227138076298266"]
meta def a512 : E := big [
  "131567475217399746230606867004698213439270903735340552877840",
  "220467727764850076301075648617352323994759446847433130433740",
  "19613773597528109457871043091789813"]
meta def b512 : E := big [
  "813086811026492741796707559955065672928733876840847771612910",
  "813514920198208771689462423142997126248302425780586032637367",
  "3596679439766472498010773471091465"]
meta def p512 : E := big [
  "106975778859322674524632700407807511783757690986197958295890",
  "880799176871822285056936075433371192216218259925744491684457",
  "759632521472231030921162532089772239092269155005006809862230",
  "149205046608119123645424042591404537029700783435116199948279",
  "666693122574035715715339776846296472848211796197116196844841",
  "478246045"]
meta def s512 : E := big [
  "239211021577334115905157219382183620200296742721559931551487",
  "588339788230133941845029203966891747887340551330352518566466",
  "269493932846928790396196999727683918070001168731410513614777",
  "289214741035657677005031701285907273102087297701867568680759",
  "428900595768973652334643953400392051674526474668616337227346",
  "166421194"]
meta def a1024 : E := big [
  "130924382471409373930766934513522929715356232117815486647321",
  "831612769103857700961938366655219197904689063149107036321635",
  "467264921256583248377715874194997833208352324721141147843596",
  "457718561444389603771522698473832995824443443784553471922769",
  "618194629653990516002732943173395535973927562271481407485365",
  "595941025"]
meta def b1024 : E := big [
  "164569583801135815680243715592668999052014296807725101348074",
  "523146097918354499422548064546975298615956175142895721356301",
  "669315076892619235533749790228381847583855957110120665158497",
  "166273615366777200186711967729562982390032945728899281035697",
  "892843460174519269746588943204189068539160919320020767560433",
  "132825929"]
meta def p1024 : E := big [
  "215461711327405620337421366597707145800596364234206331826759",
  "134186137249387175180140799674086307211555567018591461264660",
  "646950568922807022246797490990384376074214601946030151540418",
  "995532200890531388104460832177258434773432409106782899615085",
  "553028996672389929661508702575050715446998873862638404444859",
  "591463219092192595319631049266976644405125676217761899472183",
  "377665330698636120403747890079583817794426608318259540844814",
  "213953615210196833509813383078873315092728072145478324698261",
  "968793845703538278397170968929807287013220701998465096574412",
  "671219325108001704646510042997157667094192933251465479597674",
  "30649330274837225"]
meta def s1024 : E := big [
  "442243418379989499915556755967942668189442582561565222472806",
  "004214176005658062814425890045498470608287152980327255509660",
  "679689495663716833203364063537949264583920064372763054912943",
  "295973273456467310803674085179919427869131798753134404430090",
  "949531349139686915007858907151424629443598832696690956622539",
  "305890109949217805961723102614566514647001677737243109706462",
  "145402570766997679514352569983776339846534254269024215652404",
  "108480819717865237670370595679772192486732153132532467988548",
  "322791042497334592946877226747218329145013784844970716087565",
  "023463589365669129646213707081640668233472909317785263222717",
  "07721196692763666"]

/-! ## `vectors/r02.tsv` -/

-- rational_sum (eval): `1/3 + 1/6` is `1/2`
#guard evals (1 / 3 + 1 / 6) (1 / 2)

-- exact_decimal (eval): `0.1 + 0.2` is `3/10`
#guard evals (q (1 / 10) + q (1 / 5)) (3 / 10)

-- wide_integer (eval): `18446744073709551616^2` is `340282366920938463463374607...`
#guard evals (18446744073709551616 ^ 2) 340282366920938463463374607431768211456

-- negative_power (eval): `(2/3)^(-5)` is `243/32`
#guard evals ((2 / 3) ^ (-5 : ℤ)) (243 / 32)

-- precedence (eval): `-2^2 + 2^3^2` is `508`
#guard evals (-2 ^ 2 + 2 ^ (3 ^ 2 : ℕ)) 508

-- integer_product_32 (eval): `2483597973*3923401129` is `9744151091250311517`
#guard evals (2483597973 * 3923401129) 9744151091250311517

-- rational_sum_32 (eval): `2483597973/3923401129+39234...` is `21561335310528183370/974415...`
#guard evals (2483597973 / 3923401129 + 3923401129 / 2483597973)
  (21561335310528183370 / 9744151091250311517)

-- integer_product_64 (eval): `10001292739316180759*164533...` is `164555050588661611706850353...`
#guard evals (a64 * b64) p64

-- rational_sum_64 (eval): `10001292739316180759/164533...` is `370739506240069560289473947...`
#guard evals (a64 / b64 + b64 / a64) (s64 / p64)

-- integer_product_128 (eval): `239992932708435402801661488...` is `577041269174884608795396412...`
#guard evals (a128 * b128) p128

-- rational_sum_128 (eval): `239992932708435402801661488...` is `115408454547689526921527811...`
#guard evals (a128 / b128 + b128 / a128) (s128 / p128)

-- integer_product_256 (eval): `718031949919271345003672457...` is `558785550820966541079829140...`
#guard evals (a256 * b256) p256

-- rational_sum_256 (eval): `718031949919271345003672457...` is `112119348956150741133320341...`
#guard evals (a256 / b256 + b256 / a256) (s256 / p256)

-- integer_product_512 (eval): `131567475217399746230606867...` is `106975778859322674524632700...`
#guard evals (a512 * b512) p512

-- rational_sum_512 (eval): `131567475217399746230606867...` is `239211021577334115905157219...`
#guard evals (a512 / b512 + b512 / a512) (s512 / p512)

-- integer_product_1024 (eval): `130924382471409373930766934...` is `215461711327405620337421366...`
#guard evals (a1024 * b1024) p1024

-- rational_sum_1024 (eval): `130924382471409373930766934...` is `442243418379989499915556755...`
#guard evals (a1024 / b1024 + b1024 / a1024) (s1024 / p1024)

-- flat_sum_32 (eval): `1+2+3+4+5+6+7+1+2+3+4+5+6+7...` is `122`
#guard evals (flatSum 32) 122

-- balanced_sum_32 (eval): `(((((1+2)+(3+4))+((5+6)+(7+...` is `122`
#guard evals (balancedSum 5) 122

-- flat_sum_256 (eval): `1+2+3+4+5+6+7+1+2+3+4+5+6+7...` is `1018`
#guard evals (flatSum 256) 1018

-- balanced_sum_256 (eval): `((((((((1+2)+(3+4))+((5+6)+...` is `1018`
#guard evals (balancedSum 8) 1018

-- flat_sum_2048 (eval): `1+2+3+4+5+6+7+1+2+3+4+5+6+7...` is `8186`
#guard evals (flatSum 2048) 8186

-- balanced_sum_2048 (eval): `(((((((((((1+2)+(3+4))+((5+...` is `8186`
#guard evals (balancedSum 11) 8186

-- right_nested_16 (eval): `1+(1+(1+(1+(1+(1+(1+(1+(1+(...` is `17`
#guard evals (rightNested 16) 17

-- right_nested_63 (eval): `1+(1+(1+(1+(1+(1+(1+(1+(1+(...` is `64`
#guard evals (rightNested 63) 64

-- coefficient_cancellation_8 (expand): `(x+1)^8-(x+1)^8` is `0`
#guard same ((x + 1) ^ 8 - (x + 1) ^ 8) 0

-- coefficient_cancellation_32 (expand): `(x+1)^32-(x+1)^32` is `0`
#guard same ((x + 1) ^ 32 - (x + 1) ^ 32) 0

-- coefficient_cancellation_64 (expand): `(x+1)^64-(x+1)^64` is `0`
#guard same ((x + 1) ^ 64 - (x + 1) ^ 64) 0

-- coefficient_cancellation_128 (expand): `(x+1)^128-(x+1)^128` is `0`
#guard same ((x + 1) ^ 128 - (x + 1) ^ 128) 0

-- zero_division_1 (eval): `0*(1/0)` fails with `DivisionByZero`
#guard evalOf (0 * (1 / 0)) == .fault .divisionByZero

-- degree_limit_1 (expand): `x^257` fails with `ResourceLimit`
#guard E.canonAt 256 (x ^ 257) == .resourceLimit .exponent

/-! ## `vectors/cli_cases.tsv` -/

-- core/eval-adds-fractions (eval): `1/3+1/6` is `1/2`
#guard evals (1 / 3 + 1 / 6) (1 / 2)

-- core/eval-applies-power-before-negation (eval): `-2^2` is `-4`
#guard evals (-2 ^ 2) (-4)

-- core/eval-carries-past-u64 (eval): `18446744073709551615+1` is `18446744073709551616`
#guard evals (18446744073709551615 + 1) 18446744073709551616

-- core/eval-divides-negative-big-integers (eval): `(-18446744073...` is `1844674407370...`
#guard evals (-18446744073709551616 / (-1)) 18446744073709551616

-- core/eval-rejects-division-by-zero (eval): `1/0` fails with `DivisionByZero`
#guard evalOf (1 / 0) == .fault .divisionByZero

-- symbolic/simplify-collects-like-terms (simplify): `2*x+3*x+y` is `5*x + y`
#guard same (2 * x + 3 * x + y) (5 * x + y)

-- symbolic/simplify-rejects-zero-times-division-by-zero (simplify):
-- `0*(1/0)` fails with `DivisionByZero`
#guard E.canon (0 * (1 / 0)) == .fault .divisionByZero

/-! ## `vectors/library.tsv` -/

-- i04_none_simplify_w1000000 (simplify): `(-x)^2` is `(-x)^2`
#guard same ((-x) ^ 2) ((-x) ^ 2)

-- i04_none_parse_w1000000 (parse): `(-x)^2` is `((-1*x))^(2)`
#guard same ((-x) ^ 2) ((-1 * x) ^ 2)

-- i08_none_simplify_w1000000 (simplify): `(x+x)^3` is `(2*x)^3`
#guard same ((x + x) ^ 3) ((2 * x) ^ 3)

-- i08_none_parse_w1000000 (parse): `(x+x)^3` is `((2*x))^(3)`
#guard same ((x + x) ^ 3) ((2 * x) ^ 3)

-- i09_none_simplify_w1000000 (simplify): `-x` is `-x`
#guard same (-x) (-x)

-- i09_none_parse_w1000000 (parse): `-x` is `(-1*x)`
#guard same (-x) (-1 * x)

-- i10_none_simplify_w1000000 (simplify): `-x^3` is `-x^3`
#guard same (-x ^ 3) (-x ^ 3)

-- i10_none_parse_w1000000 (parse): `-x^3` is `(-1*(x)^(3))`
#guard same (-x ^ 3) (-1 * x ^ 3)

-- i11_none_simplify_w1000000 (simplify): `0` is `0`
#guard same 0 0

-- i11_none_parse_w1000000 (parse): `0` is `0`
#guard same 0 0

-- i12_none_simplify_w1000000 (simplify): `0^(-1)` fails with `DivisionByZero`
#guard E.canon (0 ^ (-1 : ℤ)) == .fault .divisionByZero

-- i13_none_simplify_w1000000 (simplify): `0^0` is `1`
#guard same (0 ^ 0) 1

-- i13_none_parse_w1000000 (parse): `0^0` is `1`
#guard same (0 ^ 0) 1

-- i15_none_simplify_w1000000 (simplify): `1/0` fails with `DivisionByZero`
#guard E.canon (1 / 0) == .fault .divisionByZero

-- i16_none_parse_w1000000 (parse): `abs(-x)` is `abs((-1*x))`
#guard same (fn "abs" (-x)) (fn "abs" (-1 * x))

-- i17_none_parse_w1000000 (parse): `abs(x)` is `abs(x)`
#guard same (fn "abs" x) (fn "abs" x)

-- i21_none_parse_w1000000 (parse): `cos(-1*x+2*x^2)` is `cos(((-1*x) + (2*(x)^(2))))`
#guard same (fn "cos" (-1 * x + 2 * x ^ 2)) (fn "cos" (-1 * x + 2 * x ^ 2))

-- i22_none_parse_w1000000 (parse): `cos(-2*x+1*x^2)` is `cos(((-2*x) + (x)^(2)))`
#guard same (fn "cos" (-2 * x + 1 * x ^ 2)) (fn "cos" (-2 * x + x ^ 2))

-- i23_none_parse_w1000000 (parse): `cos(-2*x+2*x^2)` is `cos(((-2*x) + (2*(x)^(2))))`
#guard same (fn "cos" (-2 * x + 2 * x ^ 2)) (fn "cos" (-2 * x + 2 * x ^ 2))

-- i24_none_parse_w1000000 (parse): `cos(-2*x+3*x^2)` is `cos(((-2*x) + (3*(x)^(2))))`
#guard same (fn "cos" (-2 * x + 3 * x ^ 2)) (fn "cos" (-2 * x + 3 * x ^ 2))

-- i25_none_parse_w1000000 (parse): `cos(-3*x+1*x^2)` is `cos(((-3*x) + (x)^(2)))`
#guard same (fn "cos" (-3 * x + 1 * x ^ 2)) (fn "cos" (-3 * x + x ^ 2))

-- i26_none_parse_w1000000 (parse): `cos(1*x+1*x^2)` is `cos((x + (x)^(2)))`
#guard same (fn "cos" (1 * x + 1 * x ^ 2)) (fn "cos" (x + x ^ 2))

-- i27_none_parse_w1000000 (parse): `cos(2*x)` is `cos((2*x))`
#guard same (fn "cos" (2 * x)) (fn "cos" (2 * x))

-- i28_none_parse_w1000000 (parse): `cos(2*x+3*x^2)` is `cos(((2*x) + (3*(x)^(2))))`
#guard same (fn "cos" (2 * x + 3 * x ^ 2)) (fn "cos" (2 * x + 3 * x ^ 2))

-- i29_none_parse_w1000000 (parse): `cos(3*x+1*x^2)` is `cos(((3*x) + (x)^(2)))`
#guard same (fn "cos" (3 * x + 1 * x ^ 2)) (fn "cos" (3 * x + x ^ 2))

-- i30_none_parse_w1000000 (parse): `cos(3*x+2*x^2)` is `cos(((3*x) + (2*(x)^(2))))`
#guard same (fn "cos" (3 * x + 2 * x ^ 2)) (fn "cos" (3 * x + 2 * x ^ 2))

-- i31_none_parse_w1000000 (parse): `exp(-1*x+1*x^2)` is `exp(((-1*x) + (x)^(2)))`
#guard same (fn "exp" (-1 * x + 1 * x ^ 2)) (fn "exp" (-1 * x + x ^ 2))

-- i32_none_parse_w1000000 (parse): `exp(-1*x+3*x^2)` is `exp(((-1*x) + (3*(x)^(2))))`
#guard same (fn "exp" (-1 * x + 3 * x ^ 2)) (fn "exp" (-1 * x + 3 * x ^ 2))

-- i33_none_parse_w1000000 (parse): `exp(-1*x+3*x^2)*sin(x)` is `(exp(((-1*x) + (3*(x)^(2)))...`
#guard same (fn "exp" (-1 * x + 3 * x ^ 2) * fn "sin" x)
  (fn "exp" (-1 * x + 3 * x ^ 2) * fn "sin" x)

-- i34_none_parse_w1000000 (parse): `exp(-2*x+2*x^2)*sin(x)` is `(exp(((-2*x) + (2*(x)^(2)))...`
#guard same (fn "exp" (-2 * x + 2 * x ^ 2) * fn "sin" x)
  (fn "exp" (-2 * x + 2 * x ^ 2) * fn "sin" x)

-- i35_none_parse_w1000000 (parse): `exp(-3*x+2*x^2)` is `exp(((-3*x) + (2*(x)^(2))))`
#guard same (fn "exp" (-3 * x + 2 * x ^ 2)) (fn "exp" (-3 * x + 2 * x ^ 2))

-- i36_none_parse_w1000000 (parse): `exp(-3*x+2*x^2)*sin(x)` is `(exp(((-3*x) + (2*(x)^(2)))...`
#guard same (fn "exp" (-3 * x + 2 * x ^ 2) * fn "sin" x)
  (fn "exp" (-3 * x + 2 * x ^ 2) * fn "sin" x)

-- i37_none_parse_w1000000 (parse): `exp(-3*x+3*x^2)*sin(x)` is `(exp(((-3*x) + (3*(x)^(2)))...`
#guard same (fn "exp" (-3 * x + 3 * x ^ 2) * fn "sin" x)
  (fn "exp" (-3 * x + 3 * x ^ 2) * fn "sin" x)

-- i38_none_parse_w1000000 (parse): `exp(1*x+1*x^2)` is `exp((x + (x)^(2)))`
#guard same (fn "exp" (1 * x + 1 * x ^ 2)) (fn "exp" (x + x ^ 2))

-- i39_none_parse_w1000000 (parse): `exp(1*x+2*x^2)` is `exp((x + (2*(x)^(2))))`
#guard same (fn "exp" (1 * x + 2 * x ^ 2)) (fn "exp" (x + 2 * x ^ 2))

-- i40_none_parse_w1000000 (parse): `exp(1*x+2*x^2)*sin(x)` is `(exp((x + (2*(x)^(2))))*sin...`
#guard same (fn "exp" (1 * x + 2 * x ^ 2) * fn "sin" x) (fn "exp" (x + 2 * x ^ 2) * fn "sin" x)

-- i41_none_parse_w1000000 (parse): `exp(1*x+3*x^2)*sin(x)` is `(exp((x + (3*(x)^(2))))*sin...`
#guard same (fn "exp" (1 * x + 3 * x ^ 2) * fn "sin" x) (fn "exp" (x + 3 * x ^ 2) * fn "sin" x)

-- i42_none_parse_w1000000 (parse): `exp(2*x+1*x^2)*sin(x)` is `(exp(((2*x) + (x)^(2)))*sin...`
#guard same (fn "exp" (2 * x + 1 * x ^ 2) * fn "sin" x) (fn "exp" (2 * x + x ^ 2) * fn "sin" x)

-- i43_none_parse_w1000000 (parse): `exp(2*x+2*x^2)` is `exp(((2*x) + (2*(x)^(2))))`
#guard same (fn "exp" (2 * x + 2 * x ^ 2)) (fn "exp" (2 * x + 2 * x ^ 2))

-- i44_none_parse_w1000000 (parse): `exp(2*x+2*x^2)*sin(x)` is `(exp(((2*x) + (2*(x)^(2))))...`
#guard same (fn "exp" (2 * x + 2 * x ^ 2) * fn "sin" x) (fn "exp" (2 * x + 2 * x ^ 2) * fn "sin" x)

-- i45_none_parse_w1000000 (parse): `exp(2*x+3*x^2)` is `exp(((2*x) + (3*(x)^(2))))`
#guard same (fn "exp" (2 * x + 3 * x ^ 2)) (fn "exp" (2 * x + 3 * x ^ 2))

-- i46_none_parse_w1000000 (parse): `exp(2*x+3*x^2)*sin(x)` is `(exp(((2*x) + (3*(x)^(2))))...`
#guard same (fn "exp" (2 * x + 3 * x ^ 2) * fn "sin" x) (fn "exp" (2 * x + 3 * x ^ 2) * fn "sin" x)

-- i47_none_parse_w1000000 (parse): `exp(3*x+1*x^2)` is `exp(((3*x) + (x)^(2)))`
#guard same (fn "exp" (3 * x + 1 * x ^ 2)) (fn "exp" (3 * x + x ^ 2))

-- i48_none_parse_w1000000 (parse): `exp(3*x+3*x^2)*sin(x)` is `(exp(((3*x) + (3*(x)^(2))))...`
#guard same (fn "exp" (3 * x + 3 * x ^ 2) * fn "sin" x) (fn "exp" (3 * x + 3 * x ^ 2) * fn "sin" x)

-- i50_none_parse_w1000000 (parse): `exp(sin(-1*x+1*x^2))` is `exp(sin(((-1*x) + (x)^(2))))`
#guard same (fn "exp" (fn "sin" (-1 * x + 1 * x ^ 2))) (fn "exp" (fn "sin" (-1 * x + x ^ 2)))

-- i51_none_parse_w1000000 (parse): `exp(sin(-2*x+2*x^2))` is `exp(sin(((-2*x) + (2*(x)^(2...`
#guard same (fn "exp" (fn "sin" (-2 * x + 2 * x ^ 2))) (fn "exp" (fn "sin" (-2 * x + 2 * x ^ 2)))

-- i52_none_parse_w1000000 (parse): `exp(sin(1*x+2*x^2))` is `exp(sin((x + (2*(x)^(2)))))`
#guard same (fn "exp" (fn "sin" (1 * x + 2 * x ^ 2))) (fn "exp" (fn "sin" (x + 2 * x ^ 2)))

-- i53_none_parse_w1000000 (parse): `exp(sin(2*x+1*x^2))` is `exp(sin(((2*x) + (x)^(2))))`
#guard same (fn "exp" (fn "sin" (2 * x + 1 * x ^ 2))) (fn "exp" (fn "sin" (2 * x + x ^ 2)))

-- i54_none_parse_w1000000 (parse): `exp(sin(2*x+2*x^2))` is `exp(sin(((2*x) + (2*(x)^(2)...`
#guard same (fn "exp" (fn "sin" (2 * x + 2 * x ^ 2))) (fn "exp" (fn "sin" (2 * x + 2 * x ^ 2)))

-- i55_none_parse_w1000000 (parse): `exp(sin(2*x+3*x^2))` is `exp(sin(((2*x) + (3*(x)^(2)...`
#guard same (fn "exp" (fn "sin" (2 * x + 3 * x ^ 2))) (fn "exp" (fn "sin" (2 * x + 3 * x ^ 2)))

-- i56_none_parse_w1000000 (parse): `exp(sin(3*x+2*x^2))` is `exp(sin(((3*x) + (2*(x)^(2)...`
#guard same (fn "exp" (fn "sin" (3 * x + 2 * x ^ 2))) (fn "exp" (fn "sin" (3 * x + 2 * x ^ 2)))

-- i57_none_parse_w1000000 (parse): `exp(sin(3*x+3*x^2))` is `exp(sin(((3*x) + (3*(x)^(2)...`
#guard same (fn "exp" (fn "sin" (3 * x + 3 * x ^ 2))) (fn "exp" (fn "sin" (3 * x + 3 * x ^ 2)))

-- i58_none_parse_w1000000 (parse): `exp(x)*exp(x+1)` is `(exp(x)*exp((1 + x)))`
#guard same (fn "exp" x * fn "exp" (x + 1)) (fn "exp" x * fn "exp" (1 + x))

-- i60_none_simplify_w1000000 (simplify): `i` is `i`
#guard same iu iu

-- i60_none_parse_w1000000 (parse): `i` is `i`
#guard same iu iu

-- i64_none_parse_w1000000 (parse): `log(exp(x))` is `log(exp(x))`
#guard same (fn "log" (fn "exp" x)) (fn "log" (fn "exp" x))

-- i68_none_parse_w1000000 (parse): `rootn(x,3)` is `rootn(x, 3)`
#guard same (fn2 "rootn" x 3) (fn2 "rootn" x 3)

-- i70_none_parse_w1000000 (parse): `sin(-2*x+1*x^2)` is `sin(((-2*x) + (x)^(2)))`
#guard same (fn "sin" (-2 * x + 1 * x ^ 2)) (fn "sin" (-2 * x + x ^ 2))

-- i71_none_parse_w1000000 (parse): `sin(-2*x+2*x^2)` is `sin(((-2*x) + (2*(x)^(2))))`
#guard same (fn "sin" (-2 * x + 2 * x ^ 2)) (fn "sin" (-2 * x + 2 * x ^ 2))

-- i72_none_parse_w1000000 (parse): `sin(-2*x+3*x^2)` is `sin(((-2*x) + (3*(x)^(2))))`
#guard same (fn "sin" (-2 * x + 3 * x ^ 2)) (fn "sin" (-2 * x + 3 * x ^ 2))

-- i73_none_parse_w1000000 (parse): `sin(-3*x+2*x^2)` is `sin(((-3*x) + (2*(x)^(2))))`
#guard same (fn "sin" (-3 * x + 2 * x ^ 2)) (fn "sin" (-3 * x + 2 * x ^ 2))

-- i74_none_parse_w1000000 (parse): `sin(-3*x+3*x^2)` is `sin(((-3*x) + (3*(x)^(2))))`
#guard same (fn "sin" (-3 * x + 3 * x ^ 2)) (fn "sin" (-3 * x + 3 * x ^ 2))

-- i75_none_parse_w1000000 (parse): `sin(1*x+1*x^2)` is `sin((x + (x)^(2)))`
#guard same (fn "sin" (1 * x + 1 * x ^ 2)) (fn "sin" (x + x ^ 2))

-- i76_none_parse_w1000000 (parse): `sin(1*x+2*x^2)` is `sin((x + (2*(x)^(2))))`
#guard same (fn "sin" (1 * x + 2 * x ^ 2)) (fn "sin" (x + 2 * x ^ 2))

-- i77_none_parse_w1000000 (parse): `sin(1*x+3*x^2)` is `sin((x + (3*(x)^(2))))`
#guard same (fn "sin" (1 * x + 3 * x ^ 2)) (fn "sin" (x + 3 * x ^ 2))

-- i78_none_parse_w1000000 (parse): `sin(2*x+1*x^2)` is `sin(((2*x) + (x)^(2)))`
#guard same (fn "sin" (2 * x + 1 * x ^ 2)) (fn "sin" (2 * x + x ^ 2))

-- i79_none_parse_w1000000 (parse): `sin(2*x+3*x^2)` is `sin(((2*x) + (3*(x)^(2))))`
#guard same (fn "sin" (2 * x + 3 * x ^ 2)) (fn "sin" (2 * x + 3 * x ^ 2))

-- i80_none_parse_w1000000 (parse): `sin(3*x+1*x^2)` is `sin(((3*x) + (x)^(2)))`
#guard same (fn "sin" (3 * x + 1 * x ^ 2)) (fn "sin" (3 * x + x ^ 2))

-- i81_none_parse_w1000000 (parse): `sin(x+y)` is `sin((x + y))`
#guard same (fn "sin" (x + y)) (fn "sin" (x + y))

-- i83_none_parse_w1000000 (parse): `sqrt(-x)` is `sqrt((-1*x))`
#guard same (fn "sqrt" (-x)) (fn "sqrt" (-1 * x))

-- i84_none_parse_w1000000 (parse): `sqrt(1+1*x^2)` is `sqrt((1 + (x)^(2)))`
#guard same (fn "sqrt" (1 + 1 * x ^ 2)) (fn "sqrt" (1 + x ^ 2))

-- i85_none_parse_w1000000 (parse): `sqrt(1+2*x^2)` is `sqrt((1 + (2*(x)^(2))))`
#guard same (fn "sqrt" (1 + 2 * x ^ 2)) (fn "sqrt" (1 + 2 * x ^ 2))

-- i86_none_parse_w1000000 (parse): `sqrt(1+3*x^2)` is `sqrt((1 + (3*(x)^(2))))`
#guard same (fn "sqrt" (1 + 3 * x ^ 2)) (fn "sqrt" (1 + 3 * x ^ 2))

-- i87_none_parse_w1000000 (parse): `sqrt(rootn(x,3)^2)` is `sqrt((rootn(x, 3))^(2))`
#guard same (fn "sqrt" (fn2 "rootn" x 3 ^ 2)) (fn "sqrt" (fn2 "rootn" x 3 ^ 2))

-- i88_none_parse_w1000000 (parse): `sqrt(x^2)` is `sqrt((x)^(2))`
#guard same (fn "sqrt" (x ^ 2)) (fn "sqrt" (x ^ 2))

-- i90_none_simplify_w1000000 (simplify): `x` is `x`
#guard same x x

-- i90_none_parse_w1000000 (parse): `x` is `x`
#guard same x x

-- i91_none_simplify_w1000000 (simplify): `x+x-x` is `x`
#guard same (x + x - x) x

-- i91_none_parse_w1000000 (parse): `x+x-x` is `x`
#guard same (x + x - x) x

/-! ## `vectors/root_calls.tsv` -/

-- none_parse_04 (parse): `rootn(x, 3)` is `rootn(x, 3)`
#guard same (fn2 "rootn" x 3) (fn2 "rootn" x 3)

-- none_parse_05 (parse): `rootn(x, 4)` is `rootn(x, 4)`
#guard same (fn2 "rootn" x 4) (fn2 "rootn" x 4)

-- none_parse_06 (parse): `rootn(x, 5)` is `rootn(x, 5)`
#guard same (fn2 "rootn" x 5) (fn2 "rootn" x 5)

-- none_parse_07 (parse): `rootn(x, 4096)` is `rootn(x, 4096)`
#guard same (fn2 "rootn" x 4096) (fn2 "rootn" x 4096)

-- none_parse_12 (parse): `rootn(-8, 3)` is `rootn(-8, 3)`
#guard same (fn2 "rootn" (-8) 3) (fn2 "rootn" (-8) 3)

-- none_parse_13 (parse): `rootn(-8, 4)` is `rootn(-8, 4)`
#guard same (fn2 "rootn" (-8) 4) (fn2 "rootn" (-8) 4)

-- none_parse_14 (parse): `rootn(-8, 5)` is `rootn(-8, 5)`
#guard same (fn2 "rootn" (-8) 5) (fn2 "rootn" (-8) 5)

-- none_parse_15 (parse): `rootn(-8, 4096)` is `rootn(-8, 4096)`
#guard same (fn2 "rootn" (-8) 4096) (fn2 "rootn" (-8) 4096)

-- none_parse_19 (parse): `rootn(9/4, 3)` is `rootn(9/4, 3)`
#guard same (fn2 "rootn" (9 / 4) 3) (fn2 "rootn" (9 / 4) 3)

-- none_parse_21 (parse): `rootn(x^2, 3)` is `rootn((x)^(2), 3)`
#guard same (fn2 "rootn" (x ^ 2) 3) (fn2 "rootn" (x ^ 2) 3)

-- none_parse_22 (parse): `rootn(x^2, 4)` is `rootn((x)^(2), 4)`
#guard same (fn2 "rootn" (x ^ 2) 4) (fn2 "rootn" (x ^ 2) 4)

-- none_parse_25 (parse): `sqrt(x)` is `sqrt(x)`
#guard same (fn "sqrt" x) (fn "sqrt" x)

-- none_parse_26 (parse): `sqrt(x^2)` is `sqrt((x)^(2))`
#guard same (fn "sqrt" (x ^ 2)) (fn "sqrt" (x ^ 2))

-- none_parse_29 (parse): `sqrt(2)` is `sqrt(2)`
#guard same (fn "sqrt" 2) (fn "sqrt" 2)

-- none_parse_30 (parse): `sqrt(1 - x^2)` is `sqrt((1 + (-1*(x)^(2))))`
#guard same (fn "sqrt" (1 - x ^ 2)) (fn "sqrt" (1 + -1 * x ^ 2))

-- none_parse_31 (parse): `rootn(x, 3)^3` is `x`
#guard same (fn2 "rootn" x 3 ^ 3) x

-- none_parse_32 (parse): `rootn(x, 3)^6` is `(rootn(x, 3))^(6)`
#guard same (fn2 "rootn" x 3 ^ 6) (fn2 "rootn" x 3 ^ 6)

-- none_parse_34 (parse): `rootn(x, 2)^2` is `x`
#guard same (fn2 "rootn" x 2 ^ 2) x

-- none_parse_35 (parse): `rootn(rootn(x, 3), 3)` is `rootn(rootn(x, 3), 3)`
#guard same (fn2 "rootn" (fn2 "rootn" x 3) 3) (fn2 "rootn" (fn2 "rootn" x 3) 3)

-- none_parse_36 (parse): `sqrt(rootn(x, 3))` is `sqrt(rootn(x, 3))`
#guard same (fn "sqrt" (fn2 "rootn" x 3)) (fn "sqrt" (fn2 "rootn" x 3))

-- none_parse_37 (parse): `rootn(sqrt(x), 3)` is `rootn(sqrt(x), 3)`
#guard same (fn2 "rootn" (fn "sqrt" x) 3) (fn2 "rootn" (fn "sqrt" x) 3)

-- none_parse_40 (parse): `abs(rootn(x, 3))` is `abs(rootn(x, 3))`
#guard same (fn "abs" (fn2 "rootn" x 3)) (fn "abs" (fn2 "rootn" x 3))

-- none_parse_41 (parse): `rootn(abs(x), 3)` is `rootn(abs(x), 3)`
#guard same (fn2 "rootn" (fn "abs" x) 3) (fn2 "rootn" (fn "abs" x) 3)

-- none_parse_42 (parse): `sin(rootn(x, 3))` is `sin(rootn(x, 3))`
#guard same (fn "sin" (fn2 "rootn" x 3)) (fn "sin" (fn2 "rootn" x 3))

-- none_parse_43 (parse): `rootn(x + 1, 3)*rootn(x + 1...` is `(rootn((1 + x), 3))^(2)`
#guard same (fn2 "rootn" (x + 1) 3 * fn2 "rootn" (x + 1) 3) (fn2 "rootn" (1 + x) 3 ^ 2)

-- none_parse_44 (parse): `rootn(x, 3) + rootn(x, 3) - x` is `((2*rootn(x, 3)) + (-1*x))`
#guard same (fn2 "rootn" x 3 + fn2 "rootn" x 3 - x) (2 * fn2 "rootn" x 3 + -1 * x)

-- none_parse_45 (parse): `x*rootn(x, 5)` is `(x*rootn(x, 5))`
#guard same (x * fn2 "rootn" x 5) (x * fn2 "rootn" x 5)

-- none_parse_52 (parse): `rootn(x, 300)` is `rootn(x, 300)`
#guard same (fn2 "rootn" x 300) (fn2 "rootn" x 300)

-- none_parse_53 (parse): `rootn(2, 256)` is `rootn(2, 256)`
#guard same (fn2 "rootn" 2 256) (fn2 "rootn" 2 256)

-- none_parse_58 (parse): `rootn(x, 1+2)` is `rootn(x, 3)`
#guard same (fn2 "rootn" x (1 + 2)) (fn2 "rootn" x 3)

-- none_parse_67 (parse): `sin(x)` is `sin(x)`
#guard same (fn "sin" x) (fn "sin" x)

-- none_parse_71 (parse): `acos(1/2)` is `acos(1/2)`
#guard same (fn "acos" (1 / 2)) (fn "acos" (1 / 2))

-- none_parse_73 (parse): `exp(x)` is `exp(x)`
#guard same (fn "exp" x) (fn "exp" x)

-- none_parse_75 (parse): `abs(x)` is `abs(x)`
#guard same (fn "abs" x) (fn "abs" x)

-- none_parse_76 (parse): `log(exp(x))` is `log(exp(x))`
#guard same (fn "log" (fn "exp" x)) (fn "log" (fn "exp" x))

end Kalyx.SpecTests.Terms
