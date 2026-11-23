<a id="chap-r2-values"></a>
# 4 Values and domains

This chapter gives the values that relations hold, the order on values, and the domains that a heading gives to its attributes.

Rasso has one universe of values, and a domain is a set of values. So it is in Codd’s 1970 paper, where a domain is a set, and the domains of a relation are “not necessarily distinct” [[20](references.md#codd_1970_relational.model.data.large.shared), § 1.3]. In Rasso, domains overlap: the integer $`3`$ is an element of the domain of all integers, of the range $`0..5`$, and of the set $`\{ 1, 3\}`$. There is no null value, as in The Third Manifesto [[21](references.md#date_2007_databases.types.relational.model.third)].

<a id="sec-4-1"></a>
## 4.1 Values

<a id="def-r2-value"></a>

**Definition 4.1 (Value).** ✓

> A *value* is one of these:
>
> - a Boolean, `true` or `false`;
> - an integer;
> - a rational number that is not an integer;
> - a symbol, such as `'Banana`;
> - a string;
> - a float.
>
> The *kind* of a value is the item of this list that it comes from. A symbol and a string with the same spelling are different values. $`\mathbb {V}`$ is the set of all values. Integers and the other rationals together are the *exact numbers*, the rationals $`\mathbb {Q}`$. A number has one value: $`4/2`$ is the integer $`2`$, since a domain is a set of values and the integers are a subset of the rationals.

Lean: [`Rasso.Value`](../Rasso/Value.lean#L59-L68), [`Rasso.Decimal`](../Rasso/Value.lean#L51-L57), [`Rasso.Value.ofRat`](../Rasso/Value.lean#L83-L84).

Lean holds a float as the decimal that names it: a sign, a natural number of digits, and a power of ten. Rasso compares floats, but RassoLean does not yet compute with them.

<a id="sec-4-2"></a>
## 4.2 The order on values

<a id="def-r2-order"></a>

**Definition 4.2 (Order on values).** ✓

> Values are ordered first by kind, in the order Boolean, number, symbol, string, and then within the kind: `false` before `true`, numbers (integers, rationals and floats together) as numbers, and symbols and strings by their characters. This order is a total *preorder*: equal numbers of different kinds, such as $`0`$, $`0.0`$ and $`-0.0`$, are tied. The *canonical order* breaks these ties by a fixed rule, and is a total order.

Uses: [Definition 4.1](#def-r2-value).<br>
Lean: [`Rasso.Value.cmp`](../Rasso/Value.lean#L201-L205), [`Rasso.Value.le`](../Rasso/Value.lean#L222-L223).

The comparisons $`{\lt}`$, $`\le`$, $`{\gt}`$, $`\ge`$ in terms, the aggregates `min` and `max`, and the keys of enumeration use the preorder, so $`0 {\lt} 0.0`$ is false.

<a id="sec-4-3"></a>
## 4.3 Domains

<a id="def-r2-domain"></a>

**Definition 4.3 (Domain).** ✓

> A *domain* is a set of values, written in one of three ways:
>
> - a kind (`bool`, `int`, `rat`, `symbol`, `string`, `float`): all values of that kind, where `rat` holds every exact number, integers included;
> - a range $`lo..hi`$: the integers $`n`$ with $`lo \le n \le hi`$;
> - a finite set of values, such as `{'p, 'q}`.
>
> A domain is *unmixed* when it does not hold both a float and an exact number, nor both a symbol and a string. Every domain written in a program is unmixed: RassoLean’s check of a program refuses a finite set that mixes them. So, in a program that passes the check, `=` never meets a float and an exact number, or a symbol and a string, from one domain. Membership in a domain is decidable. A program can also write a domain as `∈ R`, where `R` is a finite relation with one attribute. This domain is the finite set of values that the attribute takes in `R`.

Uses: [Definition 4.1](#def-r2-value).<br>
Lean: [`Rasso.Domain`](../Rasso/Value.lean#L279-L286), [`Rasso.Kind`](../Rasso/Value.lean#L272-L277), [`Rasso.Domain.mem`](../Rasso/Value.lean#L299-L304), [`Rasso.Domain.Unmixed`](../Rasso/Unrel.lean#L170-L175), [`Rasso.Domain.unmixed_set`](../Rasso/Unrel.lean#L189-L197).

<a id="def-r2-domain-inter"></a>

**Definition 4.4 (Finite domain; intersection).** ✓

> A domain is *finite* when it is `bool`, a range, or a finite set. The intersection of two domains is a domain when the two are the same domain, when one of them is finite, or when both are ranges, `int` or `rat`. In every other case the intersection is refused, also when the two domains share no value (for example `symbol` and `string`). A join gives each shared attribute the intersection of its two domains.

Uses: [Definition 4.3](#def-r2-domain).<br>
Lean: [`Rasso.Domain.values?`](../Rasso/Value.lean#L306-L311), [`Rasso.Domain.inter`](../Rasso/Value.lean#L316-L333).

<a id="sec-4-4"></a>
## 4.4 In $`\rho \alpha`$ and RassoLean terms

In the running example (Chapter [3](cakes.md)), the values are symbols, such as `'Banana` and `'Flour`, and integers, such as the price `400`. Rasso text writes a symbol with a leading quote, and a string in double quotes, as `"Banana"`. The decision, the number of cakes of a kind, takes values in the range `0..100`. A finite set of values is written in braces, as `{'Banana, 'Chocolate}`.

<a id="sec-4-5"></a>
## 4.5 Traditions to explore

We have yet to explore:

- typed and many-sorted presentations of the relational model, in which domains do not overlap;
- the treatment of exact and floating-point numbers together in query languages, such as SQL’s numeric types and their comparisons.

Values are what tuples hold. The next chapter gives headings, which name the attributes of a relation and give each a domain, and the tuples that fit a heading.

<a id="properties"></a>
## Properties

Each property is proved in Lean. Sketches of the proofs are in Section [A.1](proofs.md#sec-r2-proofs-values).

<a id="thm-r2-value-ofrat"></a>

**Theorem 4.5 (A number has one value).** ✓

> The map from $`\mathbb {Q}`$ to values is injective, and the exact number of the value of $`q`$ is $`q`$.

Uses: [Definition 4.1](#def-r2-value).<br>
Lean: [`Rasso.Value.ofRat_inj`](../Rasso/Value.lean#L102-L104), [`Rasso.Value.exact?_ofRat`](../Rasso/Value.lean#L95-L100).<br>
[Proof sketch](proofs.md#sketch-thm-r2-value-ofrat).

<a id="thm-r2-value-orders"></a>

**Theorem 4.6 (The orders).** ✓

> The order on values is a total preorder. The canonical order is a total order: two values that it ties are equal.

Uses: [Definition 4.2](#def-r2-order).<br>
Lean: [`Rasso.instTransCmpValueCmp`](../Rasso/Value.lean#L207), [`Rasso.instTransOrdValue`](../Rasso/Value.lean#L213-L214), [`Rasso.instLawfulEqOrdValue`](../Rasso/Value.lean#L216-L220).<br>
[Proof sketch](proofs.md#sketch-thm-r2-value-orders).

<a id="thm-r2-domain-unmixed"></a>

**Theorem 4.7 (A written domain does not mix values that $`=`$ refuses to compare).** ✓

> A domain is unmixed when it holds no exact number beside a float, and no symbol beside a string. Every kind and every range is unmixed, and so is every finite set that is accepted when it is written. On two values of an unmixed domain, `=` is equality of values.

Uses: [Definition 4.3](#def-r2-domain).<br>
Lean: [`Rasso.Domain.unmixed_kind`](../Rasso/Unrel.lean#L179-L183), [`Rasso.Domain.unmixed_range`](../Rasso/Unrel.lean#L185-L187), [`Rasso.Domain.unmixed_set`](../Rasso/Unrel.lean#L189-L197), [`Rasso.applyOp_eq_unmixed`](../Rasso/Unrel.lean#L199-L207).<br>
[Proof sketch](proofs.md#sketch-thm-r2-domain-unmixed).

<a id="thm-r2-domain-inter"></a>

**Theorem 4.8 (Finite domains and intersection).** ✓

> A finite domain lists exactly its values. When the intersection of $`a`$ and $`b`$ is defined, a value is in it exactly when it is in $`a`$ and in $`b`$, and it is finite when $`a`$ or $`b`$ is finite.

Uses: [Definition 4.4](#def-r2-domain-inter).<br>
Lean: [`Rasso.Domain.values?_sound`](../Rasso/WF.lean#L86-L108), [`Rasso.Domain.values?_complete`](../Rasso/Unrel.lean#L121-L138), [`Rasso.Domain.inter_sound`](../Rasso/WF.lean#L114-L142), [`Rasso.Domain.inter_complete`](../Rasso/Unrel.lean#L140-L168), [`Rasso.Domain.inter_finite`](../Rasso/Classes.lean#L594-L600).<br>
[Proof sketch](proofs.md#sketch-thm-r2-domain-inter).
