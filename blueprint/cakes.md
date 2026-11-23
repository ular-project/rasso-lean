<a id="chap-r2-cakes"></a>
# 3 The running example: cakes

This report uses a running example: the cake production problem of the MiniZinc handbook [[68](references.md#stuckey_2026_the.minizinc.handbook), § 2.1.2]. The Rasso paper uses it as its main example [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), § 6, Figure 6]. This chapter states the problem and gives its data.

<a id="sec-3-1"></a>
## 3.1 The problem

A bakery makes two cakes for a school fete, a banana cake and a chocolate cake. Each cake has a recipe, and the stock of each ingredient is limited. A banana cake sells for 400 cents (\$4.00) and a chocolate cake for 450 cents (\$4.50). How many of each cake should the bakery make, so that no ingredient is overused and the profit is largest?

A *batch* is one choice of how many of each cake to make, such as one banana cake and three chocolate cakes. Each batch is a candidate answer. The problem is to find, among the candidates that overuse no ingredient, the one with the largest profit.

<a id="sec-3-2"></a>
## 3.2 The data

The data is three finite relations. A program reads them as a database, which in this report we will call $`D`$. The expression `db_ref[Cakes](D)` is the relation that $`D`$ gives to the name `Cakes`, and similarly for `Recipe` and `Inventory`. Definition [6.2](finite.md#def-r2-db) defines databases and `db_ref`. Each table below gives a relation’s heading, as *attribute domain* pairs, and its tuples. The amounts are in grams, apart from bananas, which are counted. The prices are in cents.

| `Cakes` |  |
|---|---|
| `cake symbol` | `price int` |
| Banana | 400 |
| Chocolate | 450 |

| `Inventory` |  |
|---|---|
| `ingredient symbol` | `avail int` |
| Banana | 6 |
| Cocoa | 500 |
| Flour | 4000 |
| Butter | 500 |
| Sugar | 2000 |

| `Recipe` |  |  |
|---|---|---|
| `cake symbol` | `ingredient symbol` | `amount int` |
| Banana | Banana | 2 |
| Banana | Sugar | 75 |
| Banana | Flour | 250 |
| Banana | Butter | 100 |
| Chocolate | Cocoa | 75 |
| Chocolate | Sugar | 150 |
| Chocolate | Flour | 200 |
| Chocolate | Butter | 150 |

The symbol `'Banana` names a cake in `Cakes` and an ingredient in `Inventory`. The attributes keep the two apart: `cake` and `ingredient`.

<a id="sec-3-3"></a>
## 3.3 The answer

The best batch makes two banana cakes and two chocolate cakes, for a profit of $`1700`$ cents. Example [9.8](sol.md#ex-r2-cakes) gives the program that finds it. RassoLean’s evaluator and the Racket implementation both give this answer. The release’s examples hold the program and its data.
