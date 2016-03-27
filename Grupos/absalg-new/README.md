# Álgebra II
## Changes from the original absalg library

This folder contains an extension/adaptation of the [absalg](https://github.com/naftaliharris/Abstract-Algebra) python library by [Naftali Harris](http://www.naftaliharris.com) to fit our needs for the course [Algebra II](http://grados.ugr.es/matematicas/pages/infoacademica/guiasdocentes/201415/segundo/Algebra_II).

This is a sort of changelog with restpect to the original absalg module. For a short tutorial, please have a look at [Tutorial.ipynb](https://github.com/pedritomelenas/Algebra-II/blob/master/Grupos/absalg-new/Tutorial.ipynb).

### Permutations (new class)

- There is now a class of permutations. We have included a bunch of ways to define a permuation with the class `permutation`.

  - `permutation(list of integers)` creates a permutation in which the $i$ goes to the $i$th elmeent in the given list of integers.

  - `permutation(sequence of integers)` does the same as above, by considering the sequence as a list.

  - `permutation(sequence of tuples)` creates a permutation that is the product of the given tuples, by considering the tuples as cycles.

  - `permutation(list of tuples)` does the same as in the preceding case.

- Permutations have `__str__`  , `__repr__` y `__hash__`. Also

  - Equality (change this in the future)

  - Composition: p*q corresponds to (p*q)(i)=p(q(i))

  - Inverse

  - `__pow__`

  - Decomposition into disjoint_cycles

  - Number of inversions

  - Sign

  - Order

- Several groups are now defined using this class (instead of tuples).

### GroupElem

- Centralizer of the element

- Conjugacy class

- Group elements now have `repr`

- GroupElm(g,G) is now equivalent to G(g)

### Group

Now many functions are implemented using the generators of the (sub)group.

- The following optional parameters have been added to `Group`: check_ass, check_inv, identity and abelian. In this way we avoid checking the respective properties when we are sure that they hold. Among other advantages, now $S_4\times S_4$ is computed in a reasonable amount of time. Cartesian product, product of subgroups, intersection of subgroups, subroups y subgroups spanned by a list of elements take profit of this new feature.

- Cartesian product is now denoted by `G.cartesian(H)` instead of `G*H`; we keep `*` for the product of two subgroups.

- There is a new attribute for groups: `parent`. When a group is created from scratch, then `parent=self` will be set. If we create a subgroup of `G`, then `parent=G` will be set instead. This allows to easy subgroup (__le__) testings, product of elements are allowed if they are living in the same `parent` group. Also intersection of subgroups via `H.intersection(J)` is possible, and the product of subgroups `H*G`.

- The output of `G.sugroups()` is a dictionary of the form `{ n:sugroups of order n ...}`.

- Lateral classes of subgroups: `a*H` and  `H*a`.

- Cayley table now in colors if in python notebook (html object).

- There is a method to compute the set of conjugacy classes of the elements in a group; elements are used in this representation unless `rep="letters"` is used.

- Conjugacy class of a subgroup and cojugacy classes of subgroups

- Center of a group

- Normalizer and centralizer

- Search of subgroups and elements in a group with a given property

- Normal closure

- Commutator

- `orders` returns a dictionary with the orders of the elements in the group

- `group_lattice` draws the Hasse diagram of subgroups of a given group_lattice

- `CayleyGraph` displays the Cayley graph of group with respect to its generating set

- `SymmetricGroup(n)` is now a group of `permutation`s.

- We have also `AlternatingGroup(n)`, the alternating group, as a subgroup of `SymmetricGroup(n)`.

- `DihedralGroup(n)` substitutes `Dn(n)`; `DihedralGroup(n,"permutations")` ouputs the dihedral group as a subgroup of `SymmetricGroup(n)`.

- `CyclicGroup(n)` is now used instead of `Zn(n)`;  `CyclicGroup(n,"permutations")` yields the subgroup of `SymmetricGroup(n)` spanned by the cicle (1..n)

- Now a group is "callable" as explained above
```python
>>> G=SymmetricGroup(3)
>>> p=GroupElem(permutation(3,2,1),G)
>>> q=G(permutation(3,2,1))
>>> p==q
True
```

- `GroupOfUnitsModInt(n)` returns the group of units of $\mathbb{Z}_n$ (wrt multiplication).

- Groups have `__str__` y `__repr__`.


## Function

- We have introduced a new parameter `check_well_defined` to avoid testing if a function is well defined when we know (for sure) that it is so...


## GroupAction

- We introduced group actions with orbits and stabilizers

## ToDo

- Better data type control

- Tod-Coxeter algorithm: generations and relations

- Get rid of Set?
