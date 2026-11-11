//! The element and map checks of the tool: the ring axioms and the field
//! axioms, which are separate, agreement with an independent model, unique
//! stored forms, the zero test, the errors of zero divisors, the
//! characteristic, homomorphisms and parallel paths of maps, and the five
//! families of properties from fixed seeds, of which associativity,
//! commutativity and distributivity need only the ring layer and inverses
//! and canonical uniqueness the field layer.

use std::collections::BTreeMap;
use std::fmt;

use kalyx::number::Integer;
use kalyx::{Context, ErrorKind, FaultKind, Limits, Result};

use super::{
    Element, Elements, FieldLayer, FieldModel, Inspect, Lazy, Model, Modelled, Value, checked,
    exact_zero_test, failure, roomy,
};
use crate::support::{Sequence, case};

/// The cases of each family that are compared with the model.
pub const CASES: usize = 1_000;

/// The cases of each family with large operands.
pub const LARGE_CASES: usize = 50;

/// Asserts that the stored forms of `a` and `b` are the same, naming `law`.
fn assert_same<A: Inspect>(adapter: &A, a: &Element<A>, b: &Element<A>, law: &str) {
    let (left, right) = (adapter.representation(a), adapter.representation(b));
    assert!(
        left == right,
        "{}: {law} fails: {left} and {right}",
        adapter.label()
    );
}

/// The ring axioms on `elements`, for each element: $a + 0 = 0 + a = a$,
/// $a \cdot 1 = 1 \cdot a = a$, $a \cdot 0 = 0$, $a + (-a) = 0$,
/// $a - a = 0$ and $-(-a) = a$; for each triple: commutativity and
/// associativity of the sum and the product, distributivity and
/// $a - b = a + (-b)$; and $0 \ne 1$. Every result is canonical and the
/// zero test agrees with the stored forms.
pub fn ring_axioms<A: Inspect>(
    adapter: &A,
    elements: &[Element<A>],
    triples: &[(usize, usize, usize)],
) {
    let context = &mut roomy();
    let ring = Elements(adapter);
    let zero = ring.zero(context);
    let one = ring.one(context);
    assert!(!ring.same(&zero, &one), "{}: 0 = 1", adapter.label());
    assert!(exact_zero_test(adapter, &zero, context), "0 is zero");
    assert!(!exact_zero_test(adapter, &one, context), "1 is not zero");
    for (index, a) in elements.iter().enumerate() {
        case(
            Lazy(|f| {
                let a = adapter.representation(a);
                write!(f, "{}: element {index}, {a}", adapter.label())
            }),
            || {
                let context = &mut roomy();
                assert!(adapter.canonical(a), "noncanonical input");
                exact_zero_test(adapter, a, context);
                assert_same(adapter, &ring.add(a, &zero, context), a, "a + 0 = a");
                assert_same(adapter, &ring.add(&zero, a, context), a, "0 + a = a");
                assert_same(adapter, &ring.multiply(a, &one, context), a, "a 1 = a");
                assert_same(adapter, &ring.multiply(&one, a, context), a, "1 a = a");
                let product = ring.multiply(a, &zero, context);
                assert_same(adapter, &product, &zero, "a 0 = 0");
                let negation = ring.negate(a, context);
                let sum = ring.add(a, &negation, context);
                assert_same(adapter, &sum, &zero, "a + (-a) = 0");
                let difference = ring.subtract(a, a, context);
                assert_same(adapter, &difference, &zero, "a - a = 0");
                let back = ring.negate(&negation, context);
                assert_same(adapter, &back, a, "-(-a) = a");
            },
        );
    }
    for &(i, j, k) in triples {
        let (a, b, c) = (&elements[i], &elements[j], &elements[k]);
        case(
            Lazy(|f| write!(f, "{}: elements {i}, {j}, {k}", adapter.label())),
            || {
                let context = &mut roomy();
                let sum = ring.add(a, b, context);
                assert_same(adapter, &sum, &ring.add(b, a, context), "a + b = b + a");
                let product = ring.multiply(a, b, context);
                let reversed = ring.multiply(b, a, context);
                assert_same(adapter, &product, &reversed, "a b = b a");
                let bc = ring.add(b, c, context);
                let left = ring.add(&sum, c, context);
                let right = ring.add(a, &bc, context);
                assert_same(adapter, &left, &right, "(a + b) + c = a + (b + c)");
                let bc_product = ring.multiply(b, c, context);
                let left = ring.multiply(&product, c, context);
                let right = ring.multiply(a, &bc_product, context);
                assert_same(adapter, &left, &right, "(a b) c = a (b c)");
                let ac = ring.multiply(a, c, context);
                let left = ring.multiply(a, &bc, context);
                let right = ring.add(&product, &ac, context);
                assert_same(adapter, &left, &right, "a (b + c) = a b + a c");
                let negation = ring.negate(b, context);
                let left = ring.subtract(a, b, context);
                let right = ring.add(a, &negation, context);
                assert_same(adapter, &left, &right, "a - b = a + (-b)");
            },
        );
    }
}

/// The field axioms on `elements`, beyond those of the ring: for each
/// nonzero element $a a^{-1} = 1$, $(a^{-1})^{-1} = a$, $a / a = 1$ and
/// $1 / a = a^{-1}$; for each triple with a nonzero $b$, $(a / b) b = a$ and
/// $a / b = a b^{-1}$. Every result is canonical.
pub fn field_axioms<A: Inspect>(
    adapter: &A,
    elements: &[Element<A>],
    triples: &[(usize, usize, usize)],
) where
    A::Ring: FieldLayer,
{
    let context = &mut roomy();
    let ring = Elements(adapter);
    let one = ring.one(context);
    for (index, a) in elements.iter().enumerate() {
        case(
            Lazy(|f| {
                let a = adapter.representation(a);
                write!(f, "{}: element {index}, {a}", adapter.label())
            }),
            || {
                let context = &mut roomy();
                if exact_zero_test(adapter, a, context) {
                    return;
                }
                let inverse = ring.inverse(a, context);
                let product = ring.multiply(a, &inverse, context);
                assert_same(adapter, &product, &one, "a a^-1 = 1");
                let back = ring.inverse(&inverse, context);
                assert_same(adapter, &back, a, "(a^-1)^-1 = a");
                let quotient = ring.divide(a, a, context);
                assert_same(adapter, &quotient, &one, "a / a = 1");
                let quotient = ring.divide(&one, a, context);
                assert_same(adapter, &quotient, &inverse, "1 / a = a^-1");
            },
        );
    }
    for &(i, j, _) in triples {
        let (a, b) = (&elements[i], &elements[j]);
        case(
            Lazy(|f| write!(f, "{}: elements {i}, {j}", adapter.label())),
            || {
                let context = &mut roomy();
                if exact_zero_test(adapter, b, context) {
                    return;
                }
                let quotient = ring.divide(a, b, context);
                let back = ring.multiply(&quotient, b, context);
                assert_same(adapter, &back, a, "(a / b) b = a");
                let inverse = ring.inverse(b, context);
                let product = ring.multiply(a, &inverse, context);
                assert_same(adapter, &quotient, &product, "a / b = a b^-1");
            },
        );
    }
}

/// Inverting zero and dividing each of `elements` by zero fail with
/// `Fault(DivisionByZero)` without a charge, also under a bit limit of 1,
/// below every operand.
pub fn zero_divisors<A: Inspect>(adapter: &A, elements: &[Element<A>])
where
    A::Ring: FieldLayer,
{
    let zero = Elements(adapter).zero(&mut roomy());
    let ring = adapter.ring();
    let expected = ErrorKind::Fault(FaultKind::DivisionByZero);
    for bits in [1 << 16, 1] {
        let context = &mut Context::new(
            Limits::new().with_max_integer_bits(bits),
            kalyx::context::CancelFlag::new(),
        );
        let before = context.work_used();
        let error = failure("1 / 0", ring.inverse(&zero, context));
        assert_eq!(error.kind(), expected, "1 / 0 with {bits} bits");
        for a in elements {
            let error = failure("a / 0", ring.divide(a, &zero, context));
            assert_eq!(
                error.kind(),
                expected,
                "{} / 0 with {bits} bits",
                adapter.representation(a)
            );
        }
        assert_eq!(
            context.work_used(),
            before,
            "a zero divisor charges nothing"
        );
    }
}

/// The ring operations against the model of the adapter on small
/// `elements`: the images of `integers`, the zero test of each element, and
/// the sums, differences, negations and products of `pairs` agree with the
/// model; and among the first `pool` results two stored forms are equal
/// exactly when their values are.
pub fn ring_model_agreement<A: Modelled>(
    adapter: &A,
    elements: &[Element<A>],
    pairs: &[(usize, usize)],
    integers: &[i64],
    pool: usize,
) {
    let model = adapter.model();
    let ring = Elements(adapter);
    let mut results: Vec<Element<A>> = Vec::new();
    for &n in integers {
        case(Lazy(|f| write!(f, "{}: {n} * 1", adapter.label())), || {
            let context = &mut roomy();
            let image = ring.integer(&Integer::from(n), context);
            let expected = model.integer(i128::from(n));
            assert_eq!(adapter.value(&image), expected, "n * 1");
            results.push(image);
        });
    }
    for (index, a) in elements.iter().enumerate() {
        case(
            Lazy(|f| write!(f, "{}: zero test of element {index}", adapter.label())),
            || {
                let context = &mut roomy();
                let expected = adapter.value(a) == model.zero();
                assert_eq!(exact_zero_test(adapter, a, context), expected, "zero test");
            },
        );
    }
    for &(i, j) in pairs {
        let (a, b) = (&elements[i], &elements[j]);
        case(
            Lazy(|f| {
                let label = adapter.label();
                write!(f, "{label} against {}: elements {i}, {j}", model.label())
            }),
            || {
                let context = &mut roomy();
                let (x, y) = (adapter.value(a), adapter.value(b));
                let sum = ring.add(a, b, context);
                assert_eq!(adapter.value(&sum), model.add(&x, &y), "a + b");
                let difference = ring.subtract(a, b, context);
                assert_eq!(adapter.value(&difference), model.subtract(&x, &y), "a - b");
                let negation = ring.negate(a, context);
                assert_eq!(adapter.value(&negation), model.negate(&x), "-a");
                let product = ring.multiply(a, b, context);
                assert_eq!(adapter.value(&product), model.multiply(&x, &y), "a b");
                results.extend([sum, difference, negation, product]);
            },
        );
    }
    results.truncate(pool);
    let representations: Vec<String> = results.iter().map(|r| adapter.representation(r)).collect();
    let values: Vec<String> = results
        .iter()
        .map(|r| adapter.value(r).to_string())
        .collect();
    unique_forms(&adapter.label(), &representations, &values);
}

/// The quotients and inverses against the model of the adapter on small
/// `elements`: for each of `pairs` with a nonzero second element $b$,
/// $a / b$ and $b^{-1}$ agree with the model.
pub fn field_model_agreement<A: Modelled>(
    adapter: &A,
    elements: &[Element<A>],
    pairs: &[(usize, usize)],
) where
    A::Ring: FieldLayer,
    A::Model: FieldModel,
{
    let model = adapter.model();
    let ring = Elements(adapter);
    for &(i, j) in pairs {
        let (a, b) = (&elements[i], &elements[j]);
        case(
            Lazy(|f| {
                let label = adapter.label();
                write!(f, "{label} against {}: elements {i}, {j}", model.label())
            }),
            || {
                let context = &mut roomy();
                let (x, y) = (adapter.value(a), adapter.value(b));
                let Some(inverse) = model.inverse(&y) else {
                    assert!(exact_zero_test(adapter, b, context), "b is zero");
                    return;
                };
                let quotient = ring.divide(a, b, context);
                assert_eq!(
                    adapter.value(&quotient),
                    model.multiply(&x, &inverse),
                    "a / b"
                );
                let actual = ring.inverse(b, context);
                assert_eq!(adapter.value(&actual), inverse, "1 / b");
            },
        );
    }
}

/// Two stored forms among the results are the same exactly when their
/// values are: `representations[i]` and `values[i]` describe result `i`,
/// and each determines the other.
pub fn unique_forms(label: &str, representations: &[String], values: &[String]) {
    assert_eq!(representations.len(), values.len());
    let mut by_form: BTreeMap<&str, &str> = BTreeMap::new();
    let mut by_value: BTreeMap<&str, &str> = BTreeMap::new();
    for (form, value) in representations.iter().zip(values) {
        let known = by_form.entry(form).or_insert(value);
        assert_eq!(
            known, value,
            "{label}: the stored form {form} has the values {known} and {value}"
        );
        let known = by_value.entry(value).or_insert(form);
        assert_eq!(
            known, form,
            "{label}: the value {value} has the stored forms {known} and {form}"
        );
    }
}

/// Characteristic zero: the image $n \cdot 1$ of each nonzero integer of
/// `integers` is nonzero and agrees with the model.
pub fn characteristic_zero<A: Modelled>(adapter: &A, integers: &[i64]) {
    assert_eq!(adapter.characteristic(), 0, "{}", adapter.label());
    let ring = Elements(adapter);
    let mut checked = 0;
    for &n in integers.iter().filter(|&&n| n != 0) {
        let context = &mut roomy();
        let image = ring.integer(&Integer::from(n), context);
        assert!(
            !exact_zero_test(adapter, &image, context),
            "{}: {n} * 1 = 0",
            adapter.label()
        );
        let expected = adapter.model().integer(i128::from(n));
        assert_eq!(adapter.value(&image), expected, "{n} * 1");
        checked += 1;
    }
    assert!(checked > 0, "a nonzero integer is checked");
}

/// A map from a source value into a target, on a context.
pub type Map<'a, S, T> = &'a dyn Fn(&S, &mut Context) -> Result<T>;

/// Checks that `map` from the model `source` into the parent of `target` is
/// a ring homomorphism on `values`: it maps zero and one to zero and one,
/// and preserves the sums, differences, negations and products of `pairs`,
/// compared by the stored forms of the target. Every image is canonical.
pub fn homomorphism<S: Model, A: Inspect>(
    source: &S,
    target: &A,
    map: Map<'_, S::Value, Element<A>>,
    values: &[S::Value],
    pairs: &[(usize, usize)],
) {
    let label = format!("map from {} to {}", source.label(), target.label());
    let image =
        |value: &S::Value, context: &mut Context| checked(target, "the image", map(value, context));
    let ring = Elements(target);
    let context = &mut roomy();
    let zero = image(&source.zero(), context);
    assert_same(
        target,
        &zero,
        &ring.zero(context),
        &format!("{label}: f(0) = 0"),
    );
    let one = image(&source.one(), context);
    assert_same(
        target,
        &one,
        &ring.one(context),
        &format!("{label}: f(1) = 1"),
    );
    for &(i, j) in pairs {
        let (a, b) = (&values[i], &values[j]);
        case(
            Lazy(|f| write!(f, "{label}: values {i}, {j}: {a} and {b}")),
            || {
                let context = &mut roomy();
                let (x, y) = (image(a, context), image(b, context));
                let mapped = image(&source.add(a, b), context);
                let expected = ring.add(&x, &y, context);
                assert_same(target, &mapped, &expected, "f(a + b) = f(a) + f(b)");
                let mapped = image(&source.subtract(a, b), context);
                let expected = ring.subtract(&x, &y, context);
                assert_same(target, &mapped, &expected, "f(a - b) = f(a) - f(b)");
                let mapped = image(&source.negate(a), context);
                let expected = ring.negate(&x, context);
                assert_same(target, &mapped, &expected, "f(-a) = -f(a)");
                let mapped = image(&source.multiply(a, b), context);
                let expected = ring.multiply(&x, &y, context);
                assert_same(target, &mapped, &expected, "f(a b) = f(a) f(b)");
            },
        );
    }
}

/// A named map from a source value into a target.
pub type Path<'a, S, T> = (&'a str, Map<'a, S, T>);

/// Checks that the parallel `paths` between the same two structures define
/// the same map on `values`: their images have the same stored form in
/// `target`.
pub fn commuting_paths<S: fmt::Debug, A: Inspect>(
    target: &A,
    values: &[S],
    paths: &[Path<'_, S, Element<A>>],
) {
    for (index, a) in values.iter().enumerate() {
        let (first, map) = paths[0];
        let expected = checked(target, first, map(a, &mut roomy()));
        for &(name, map) in &paths[1..] {
            case(
                Lazy(|f| write!(f, "value {index}, {a:?}: {first} and {name}")),
                || {
                    let image = checked(target, name, map(a, &mut roomy()));
                    assert_same(target, &image, &expected, "parallel paths agree");
                },
            );
        }
    }
}

// ---------------------------------------------------------------------------
// The five families from fixed seeds

fn assert_agrees<A: Modelled>(adapter: &A, a: &Element<A>, value: &Value<A>, what: &str) {
    assert!(
        adapter.agrees(a, value),
        "{what}: {} is not {value}",
        adapter.text(a)
    );
}

/// A sampled value with its element, which the adapter builds.
fn sample<A: Modelled>(adapter: &A, random: &mut Sequence) -> (Element<A>, Value<A>) {
    let value = adapter.sample(random);
    (adapter.element(&value), value)
}

/// The element of `value`, built in the field as $n \cdot 1 / d \cdot 1$.
fn field_element<A: Modelled>(adapter: &A, value: &Value<A>, context: &mut Context) -> Element<A>
where
    A::Ring: FieldLayer,
    A::Model: FieldModel,
{
    let ring = Elements(adapter);
    let (n, d) = adapter.model().fraction(value, 1);
    let n = ring.integer(&n, context);
    let d = ring.integer(&d, context);
    ring.divide(&n, &d, context)
}

/// A sampled value with its element, built in the field.
fn field_sample<A: Modelled>(
    adapter: &A,
    random: &mut Sequence,
    context: &mut Context,
) -> (Element<A>, Value<A>)
where
    A::Ring: FieldLayer,
    A::Model: FieldModel,
{
    let value = adapter.sample(random);
    (field_element(adapter, &value, context), value)
}

/// The image of the fresh random integer `random.next() | low_bit`, drawn
/// again while the image is zero, which can happen only in a ring of
/// positive characteristic.
fn nonzero_image<A: Inspect>(
    adapter: &A,
    random: &mut Sequence,
    low_bit: u64,
    context: &mut Context,
) -> Element<A> {
    loop {
        let image = Elements(adapter).integer(&Integer::from(random.next() | low_bit), context);
        if !exact_zero_test(adapter, &image, context) {
            return image;
        }
    }
}

/// A large element built in the field: the product of four quotients of
/// 64-bit integer images, negated half the time.
fn field_large<A: Inspect>(adapter: &A, random: &mut Sequence, context: &mut Context) -> Element<A>
where
    A::Ring: FieldLayer,
{
    let ring = Elements(adapter);
    let mut product = ring.one(context);
    for _ in 0..4 {
        let n = nonzero_image(adapter, random, 0, context);
        let d = nonzero_image(adapter, random, 1, context);
        let quotient = ring.divide(&n, &d, context);
        product = ring.multiply(&product, &quotient, context);
    }
    if random.index(2) == 0 {
        ring.negate(&product, context)
    } else {
        product
    }
}

/// $(a + b) + c = a + (b + c)$ and $(a b) c = a (b c)$: 1,000 cases from
/// `seed` against the model, then large operands by the identities alone.
pub fn associativity<A: Modelled>(adapter: &A, seed: u64) {
    let model = adapter.model();
    let ring = Elements(adapter);
    let mut random = Sequence::new(seed);
    let c = &mut roomy();
    for _ in 0..CASES {
        let (a, av) = sample(adapter, &mut random);
        let (b, bv) = sample(adapter, &mut random);
        let (d, dv) = sample(adapter, &mut random);
        let ab = ring.add(&a, &b, c);
        let left = ring.add(&ab, &d, c);
        let bd = ring.add(&b, &d, c);
        let right = ring.add(&a, &bd, c);
        let expected = model.add(&model.add(&av, &bv), &dv);
        assert_agrees(adapter, &left, &expected, "(a + b) + c");
        assert_agrees(adapter, &right, &expected, "a + (b + c)");
        let ab = ring.multiply(&a, &b, c);
        let left = ring.multiply(&ab, &d, c);
        let bd = ring.multiply(&b, &d, c);
        let right = ring.multiply(&a, &bd, c);
        let expected = model.multiply(&model.multiply(&av, &bv), &dv);
        assert_agrees(adapter, &left, &expected, "(a b) c");
        assert_agrees(adapter, &right, &expected, "a (b c)");
    }
    for _ in 0..LARGE_CASES {
        let (a, b, d) = (
            adapter.large(&mut random),
            adapter.large(&mut random),
            adapter.large(&mut random),
        );
        let ab = ring.add(&a, &b, c);
        let left = ring.add(&ab, &d, c);
        let bd = ring.add(&b, &d, c);
        let right = ring.add(&a, &bd, c);
        assert!(ring.equal(&left, &right, c), "(a + b) + c = a + (b + c)");
        let ab = ring.multiply(&a, &b, c);
        let left = ring.multiply(&ab, &d, c);
        let bd = ring.multiply(&b, &d, c);
        let right = ring.multiply(&a, &bd, c);
        assert!(ring.equal(&left, &right, c), "(a b) c = a (b c)");
        assert_same(adapter, &left, &right, "(a b) c = a (b c)");
    }
}

/// $a + b = b + a$ and $a b = b a$, with $a - b$ against the model.
pub fn commutativity<A: Modelled>(adapter: &A, seed: u64) {
    let model = adapter.model();
    let ring = Elements(adapter);
    let mut random = Sequence::new(seed);
    let c = &mut roomy();
    for _ in 0..CASES {
        let (a, av) = sample(adapter, &mut random);
        let (b, bv) = sample(adapter, &mut random);
        let expected = model.add(&av, &bv);
        assert_agrees(adapter, &ring.add(&a, &b, c), &expected, "a + b");
        assert_agrees(adapter, &ring.add(&b, &a, c), &expected, "b + a");
        let expected = model.multiply(&av, &bv);
        assert_agrees(adapter, &ring.multiply(&a, &b, c), &expected, "a b");
        assert_agrees(adapter, &ring.multiply(&b, &a, c), &expected, "b a");
        let expected = model.subtract(&av, &bv);
        assert_agrees(adapter, &ring.subtract(&a, &b, c), &expected, "a - b");
    }
    for _ in 0..LARGE_CASES {
        let (a, b) = (adapter.large(&mut random), adapter.large(&mut random));
        let left = ring.add(&a, &b, c);
        let right = ring.add(&b, &a, c);
        assert_same(adapter, &left, &right, "a + b = b + a");
        let left = ring.multiply(&a, &b, c);
        let right = ring.multiply(&b, &a, c);
        assert_same(adapter, &left, &right, "a b = b a");
    }
}

/// $a (b + c) = a b + a c$ and $(a - b) c = a c - b c$.
pub fn distributivity<A: Modelled>(adapter: &A, seed: u64) {
    let model = adapter.model();
    let ring = Elements(adapter);
    let mut random = Sequence::new(seed);
    let c = &mut roomy();
    for _ in 0..CASES {
        let (a, av) = sample(adapter, &mut random);
        let (b, bv) = sample(adapter, &mut random);
        let (d, dv) = sample(adapter, &mut random);
        let bd = ring.add(&b, &d, c);
        let left = ring.multiply(&a, &bd, c);
        let ab = ring.multiply(&a, &b, c);
        let ad = ring.multiply(&a, &d, c);
        let right = ring.add(&ab, &ad, c);
        let expected = model.multiply(&av, &model.add(&bv, &dv));
        assert_agrees(adapter, &left, &expected, "a (b + c)");
        assert_agrees(adapter, &right, &expected, "a b + a c");
        let difference = ring.subtract(&a, &b, c);
        let left = ring.multiply(&difference, &d, c);
        let ad = ring.multiply(&a, &d, c);
        let bd = ring.multiply(&b, &d, c);
        let right = ring.subtract(&ad, &bd, c);
        let expected = model.multiply(&model.subtract(&av, &bv), &dv);
        assert_agrees(adapter, &left, &expected, "(a - b) c");
        assert_agrees(adapter, &right, &expected, "a c - b c");
    }
    for _ in 0..LARGE_CASES {
        let (a, b, d) = (
            adapter.large(&mut random),
            adapter.large(&mut random),
            adapter.large(&mut random),
        );
        let bd = ring.add(&b, &d, c);
        let left = ring.multiply(&a, &bd, c);
        let ab = ring.multiply(&a, &b, c);
        let ad = ring.multiply(&a, &d, c);
        let right = ring.add(&ab, &ad, c);
        assert!(ring.equal(&left, &right, c), "a (b + c) = a b + a c");
        assert_same(adapter, &left, &right, "a (b + c) = a b + a c");
    }
}

/// $a + (-a) = 0$, $-(-a) = a$, $a a^{-1} = 1$ and $a / b = a b^{-1}$ for
/// $b \ne 0$; the inverse of zero and a quotient by zero fail with
/// `DivisionByZero` before any charge. The sampled elements are built in the
/// field.
pub fn inverses<A: Modelled>(adapter: &A, seed: u64)
where
    A::Ring: FieldLayer,
    A::Model: FieldModel,
{
    let model = adapter.model();
    let ring = Elements(adapter);
    let mut random = Sequence::new(seed);
    let c = &mut roomy();
    let mut zeros = 0;
    for _ in 0..CASES {
        let (a, av) = field_sample(adapter, &mut random, c);
        let (b, bv) = field_sample(adapter, &mut random, c);
        let negated = ring.negate(&a, c);
        assert_agrees(adapter, &negated, &model.negate(&av), "-a");
        let sum = ring.add(&a, &negated, c);
        assert!(exact_zero_test(adapter, &sum, c), "a + (-a) is zero");
        assert_agrees(adapter, &sum, &model.zero(), "a + (-a)");
        assert_agrees(adapter, &ring.negate(&negated, c), &av, "-(-a)");
        assert_eq!(exact_zero_test(adapter, &a, c), av == model.zero());
        match model.inverse(&av) {
            Some(inverse) => {
                let actual = ring.inverse(&a, c);
                assert_agrees(adapter, &actual, &inverse, "1 / a");
                let one = ring.multiply(&a, &actual, c);
                assert_agrees(adapter, &one, &model.one(), "a (1 / a)");
            }
            None => {
                zeros += 1;
                let before = c.work_used();
                let expected = ErrorKind::Fault(FaultKind::DivisionByZero);
                let error = failure("1 / 0", adapter.ring().inverse(&a, c));
                assert_eq!(error.kind(), expected);
                let error = failure("b / 0", adapter.ring().divide(&b, &a, c));
                assert_eq!(error.kind(), expected);
                assert_eq!(c.work_used(), before);
            }
        }
        if let Some(inverse) = model.inverse(&bv) {
            let quotient = ring.divide(&a, &b, c);
            let expected = model.multiply(&av, &inverse);
            assert_agrees(adapter, &quotient, &expected, "a / b");
            let product = ring.multiply(&a, &ring.inverse(&b, c), c);
            assert_same(adapter, &quotient, &product, "a / b = a b^-1");
        }
    }
    assert!(zeros > 0, "the sample holds zeros");
    let zero = ring.zero(c);
    let one = ring.one(c);
    for _ in 0..LARGE_CASES {
        let a = field_large(adapter, &mut random, c);
        let inverse = ring.inverse(&a, c);
        let product = ring.multiply(&a, &inverse, c);
        assert!(ring.equal(&product, &one, c), "a a^-1 = 1");
        assert_same(adapter, &product, &one, "a a^-1 = 1");
        let negated = ring.negate(&a, c);
        let sum = ring.add(&a, &negated, c);
        assert_same(adapter, &sum, &zero, "a + (-a) = 0");
        assert!(adapter.ring().divide(&a, &zero, c).is_err(), "a / 0");
    }
}

/// Equal values built in different ways have the same stored form and the
/// same display text: $(n k) / (d k)$, $n \cdot d^{-1}$, $-((-n k) / (d k))$
/// and $(x + w) - w$.
pub fn canonical_uniqueness<A: Modelled>(adapter: &A, seed: u64)
where
    A::Ring: FieldLayer,
    A::Model: FieldModel,
{
    let model = adapter.model();
    let ring = Elements(adapter);
    let mut random = Sequence::new(seed);
    let c = &mut roomy();
    for _ in 0..CASES {
        let value = adapter.sample(&mut random);
        // A scale whose image is nonzero, which only a field of positive
        // characteristic can fail to give.
        let scale = loop {
            let k = random.next_in(1, 1 << 15);
            let image = ring.integer(&Integer::from(k), c);
            if !exact_zero_test(adapter, &image, c) {
                break k;
            }
        };
        let (n, d) = model.fraction(&value, scale);
        let n_image = ring.integer(&n, c);
        let d_image = ring.integer(&d, c);
        let scaled = ring.divide(&n_image, &d_image, c);
        let (n, d) = model.fraction(&value, 1);
        let n_image = ring.integer(&n, c);
        let d_image = ring.integer(&d, c);
        let inverted = ring.multiply(&n_image, &ring.inverse(&d_image, c), c);
        let (n, d) = model.fraction(&model.negate(&value), scale);
        let n_image = ring.integer(&n, c);
        let d_image = ring.integer(&d, c);
        let negated = ring.negate(&ring.divide(&n_image, &d_image, c), c);
        let (w, _) = field_sample(adapter, &mut random, c);
        let shifted = ring.subtract(&ring.add(&scaled, &w, c), &w, c);
        for other in [&inverted, &negated, &shifted] {
            assert_same(adapter, &scaled, other, "one stored form per value");
            assert_eq!(adapter.text(&scaled), adapter.text(other));
            assert!(ring.equal(&scaled, other, c));
        }
        assert_agrees(adapter, &scaled, &value, "(n k) / (d k)");
    }
    for _ in 0..LARGE_CASES {
        let (a, b) = (
            field_large(adapter, &mut random, c),
            field_large(adapter, &mut random, c),
        );
        let product = ring.multiply(&a, &b, c);
        let back = ring.divide(&product, &b, c);
        assert_same(adapter, &back, &a, "(a b) / b = a");
        assert_eq!(adapter.text(&back), adapter.text(&a));
    }
}
