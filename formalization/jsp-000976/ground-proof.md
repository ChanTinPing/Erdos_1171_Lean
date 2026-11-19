# A direct proof of Erdős #1171

The statement is Theorem 1.1 of Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer, *A finite-color partition relation for ω₁²*. The argument below is verified in [Theorem.lean](Jsp000976/Theorem.lean). [Preprint, Hexagon 2611.00584v1](https://hexagonmath.org/2611.00584v1)

## Comparison with the preprint

| Preprint | Lean proof in this repository |
| --- | --- |
| §§2–3 reduce the problem to nested colorings and establish backward incidence in a full region. | Retains both reductions, with the ordinal geometry and the final passage back to unordered pair colorings formalized explicitly. The thinning lemma works on indexed slice families, so distinct labels may share a row. [Thinning](Jsp000976/Thinning.lean) · [Incidence](Jsp000976/Incidence.lean) |
| §4 builds a countable reservoir tree, prunes it using one point and an additional color at each node, and uses a category hypothesis to choose one branch meeting all finite tests. | Keeps full children by proving the choice for each finite test locally. Uses the set of marked colors as a node's type and retains all candidate labels of one dense type. Each finite test has its own infinite prefix chain. [Reservoir tree](Jsp000976/PrunedFamilies.lean) · [Dense types](Jsp000976/DenseCone.lean) |
| §4 minimizes the positive palette of a stock taken from that branch and enlarges the marked set. | Generates a proper ideal from old mark sets and sets containing no infinite prefix chain. Thins and minimizes the palette on comparable labels. Each positive family contains an infinite chain, which gives a stock when needed. [Chain ideal](Jsp000976/ChainIdeal.lean) · [Comparable palette](Jsp000976/CompatiblePalette.lean) |
| §5 uses Cohen forcing to obtain the category hypothesis and reflects the resulting stock to the ground model. | Proves the marking induction directly using finite tests and the chain ideal. The final Lean theorem has no forcing or category assumptions. [Marking step](Jsp000976/GroundStep.lean) |

Let a **stock** have uncountable slices in an increasing sequence of rows of length `ω`. Work under the assumption that a nested coloring has neither a positive monochromatic triangle nor a zero stock. Fix the full set `X` with the incidence property from the paper. In particular, for any thick slice of `X`, the later vertices with only countably many positive neighbors in the slice form a small set.

## Marking data on indexed slices

In the induction, replace the stock in each reservoir with a countable indexed family of thick slices. Labels can share a physical row. The data include a common cutoff, a proper ideal on the labels containing the finite sets, and a finite set of positive colors `L`. For every `y ∈ X` above the cutoff and every `ℓ ∈ L`, the set of labels whose `ℓ`-fibers at `y` are uncountable belongs to the ideal.

Any full reservoir has data with no marked colors, using the slices of an ordinary stock and the finite-set ideal. Data marking every positive color are impossible. Choose a point above the cutoff that has an uncountable positive fiber on every indexed slice, using the countable union of small exceptions. In each slice some positive color then has an uncountable fiber. The finitely many corresponding mark sets cover all the labels, contradicting properness of the ideal.

## Ground-model rank step

At a node with full reservoir `Y_s`, let the child indexed by label `a` keep the points of `Y_s` above the parent cutoff at which all marked fibers into slice `a` are countable. Keep the children with full reservoirs.

Every finite test of later points can be met by a full child. Choose a point `y` in the parent's full tail outside every nonfull candidate child, using the countable closure of small sets. The parent's proper ideal gives a label avoiding all marks at `y` and all marks in the finite test. The child for this label contains `y`, so it is full. The retained children are nonempty and countable at every node, and can be enumerated by naturals. The entire resulting tree is countable, so one ordinal `γ*` bounds all its cutoffs.

Tag each node by its marked set. Some tag `L` is dense in a cone of the tree. In that cone every prefix extends to a node tagged `L`. To see this, if no tag has such a cone, refine successively to a cone excluding each of the finitely many tags. The final cone would contain a node without a tag.

A candidate's label is the path through a node tagged `L`, including its chosen child step. Its slice is the thick slice selected by that child. Order the labels by proper prefix. The physical rows increase along this order. For comparable labels, the later slice lies in the earlier label's chosen child reservoir, so its backward degrees into the earlier slice in colors from `L` are countable. The forward degrees are countable by nesting. Thin all candidate slices at once, forbidding `L` edges only between comparable labels.

Call a label set chain-free if it contains no infinite sequence increasing in the proper-prefix order. Chain-free sets form an ideal because an infinite chain through a union of two sets contains an infinite subchain in one of them. Every finite label set is chain-free. Generate a new ideal `J` from all chain-free sets and all old mark sets after thinning. It is proper. For any finite list of old marks, extend the current path to a node of the chosen type, then select a child avoiding all marks in the list. Iteration yields an infinite chain disjoint from their union, so adding any chain-free set still cannot cover all candidate labels.

On a `J`-positive subfamily with possibly smaller thick slices, define the internal palette using positive edges between **comparable** labels. Choose such a subfamily with minimum palette size. Its palette `P` is nonempty. A `J`-positive family contains an infinite chain, which would yield a zero stock if `P` were empty, since every individual slice is zero by nesting. Also `P ∩ L = ∅` by the simultaneous thinning.

For any `p ∈ P` and any `y ∈ X` above `γ*`, suppose the labels with thick `p`-fibers at `y` are `J`-positive. Restrict to those labels and to those fibers. This deletes color `p` from the comparable-pair palette by triangle exclusion, contradicting minimality. Thus every color in `P` satisfies the mark condition. Restrict the ideal to the selected positive family. Old marks remain small by thinning, and the new family marks `L ∪ P`. Its slices are in the original full reservoir and its cutoff is `γ*`.

Iteration up to the number of positive colors contradicts the all-marked obstruction. The nested reduction and the ordinal grid isomorphism then give the original relation.
