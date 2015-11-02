"""Group implementation"""

import itertools
import functools
import operator
from Set import Set
from Function import Function
from fractions import gcd

class GroupElem:
    """
    Group element definition

    This is mainly syntactic sugar, so you can write stuff like g * h
    instead of group.bin_op(g, h), or group(g, h).
    """

    def __init__(self, elem, group):
        if not isinstance(group, Group):
            raise TypeError("group is not a Group")
        if not elem in group.Set:
            raise TypeError("elem is not an element of group")
        self.elem = elem
        self.group = group

    def __str__(self):
        return str(self.elem)

    def __repr__(self):
        return repr(self.elem)

    def __eq__(self, other):
        """
        Two GroupElems are equal if they represent the same element in the same group
        """

        if not isinstance(other, GroupElem):
            return False #raise TypeError("other is not a GroupElem")
        return (self.elem == other.elem) and (self.group.parent==other.group.parent)

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(self.elem)

    def __mul__(self, other):
        """
        If other is a group element, returns self * other.
        If other = n is an int, and self is in an abelian group, returns self**n
        """

        if isinstance(other,Group) or isinstance(other,set):
            return set([self*g for g in other])
        if self.group.is_abelian() and isinstance(other, (int)):
            return self ** other

        if not isinstance(other, GroupElem):
            raise TypeError("other must be a GroupElem, or an int " \
                            "(if self's group is abelian)")
        if not(self.group.parent==other.group.parent):
            raise TypeError("both elements must be in the same group")
        try:
            return GroupElem(self.group.parent.bin_op((self.elem, other.elem)), \
                             self.group.parent)
        # This can return a TypeError in Funcion.__call__ if self and other
        # belong to different Groups. So we see if we can make sense of this
        # operation the other way around.
        except TypeError:
            return other.__rmul__(self)

    def __rmul__(self, other):
        """
        If other is a group element, returns other * self.
        If other = n is an int, and self is in an abelian group, returns self**n
        """
        if self.group.is_abelian() and isinstance(other, (int)):
            return self ** other

        if not isinstance(other, GroupElem):
            raise TypeError("other must be a GroupElem, or an int " \
                            "(if self's group is abelian)")

        return GroupElem(self.group.bin_op((other.elem, self.elem)), self.group)

    def __add__(self, other):
        """Returns self + other for Abelian groups"""
        if self.group.is_abelian():
            return self * other
        raise TypeError("not an element of an abelian group")

    def __pow__(self, n, modulo=None):
        """
        Returns self**n

        modulo is included as an argument to comply with the API, and ignored
        """
        if not (isinstance(n, int)):
            raise TypeError("n must be an int or a long")

        if n == 0:
            return self.group.e
        elif n < 0:
            return self.group.inverse(self) ** -n
        elif n % 2 == 1:
            return self * (self ** (n - 1))
        else:
            return (self * self) ** (n // 2)

    def __neg__(self):
        """Returns self ** -1 if self is in an abelian group"""
        if not self.group.is_abelian():
            raise TypeError("self must be in an abelian group")
        return self ** (-1)

    def __sub__(self, other):
        """Returns self * (other ** -1) if self is in an abelian group"""
        if not self.group.is_abelian():
            raise TypeError("self must be in an abelian group")
        return self * (other ** -1)

    def conjugacy_class(self):
        """
        Returns the conjugacy class of self in self.group
        """
        return frozenset([g*self*g**-1 for g in self.group])

    def centralizer(self):
        """
        Returns the centralizer of self, that is, the set of elements that commute with self
        """
        G=Set([g.elem for g in self.group if g*self==self*g])
        op=self.group.bin_op.new_domains(G.cartesian(G),G) #Function(G.cartesian(G),G,lambda x:x[0]*x[1])
        return Group(G,op,parent=self.group.parent, check_ass=False, check_inv=False, abelian=self.group.is_abelian(),identity=self.group.e.elem)

    def order(self):
        """Returns the order of self in the Group"""
        return len(self.group.generate([self]))


class Group:
    """Group definition"""
    def __init__(self, G, bin_op, parent=None, check_ass=True, check_inv=True, identity=None, abelian=None):
        """Create a group, checking group axioms"""

        # Test types
        if not isinstance(G, Set): raise TypeError("G must be a set")
        if not isinstance(bin_op, Function):
            raise TypeError("bin_op must be a function")
        if bin_op.codomain != G:
            raise TypeError("binary operation must have codomain equal to G")
        if bin_op.domain != G.cartesian(G):
            raise TypeError("binary operation must have domain equal to G x G")
        if not(isinstance(check_ass,bool)):
            raise TypeError("check_ass must be bool")
        if not(isinstance(check_inv,bool)):
            raise TypeError("check_inv must be bool")


        # Test associativity
        if check_ass:
            if not all(bin_op((a, bin_op((b, c)))) == \
                       bin_op((bin_op((a, b)), c)) \
                       for a in G for b in G for c in G):
                raise ValueError("binary operation is not associative")
        # Find the identity
        if identity in G:
            e=identity
        else:
            found_id = False
            for e in G:
                if all(bin_op((e, a)) == a for a in G):
                    found_id = True
                    break
            if not found_id:
                raise ValueError("G doesn't have an identity")

        # Test for inverses
        if check_inv:
            for a in G:
                if not any(bin_op((a,  b)) == e for b in G):
                    raise ValueError("G doesn't have inverses")

        # At this point, we've verified that we have a Group.
        # Now determine if the Group is abelian:
        if not(isinstance(abelian,bool)):
            self.abelian = all(bin_op((a, b)) == bin_op((b, a)) \
                               for a in G for b in G)
        else:
            self.abelian=abelian
        self.Set = G
        self.group_elems = Set(GroupElem(g, self) for g in G)
        self.e = GroupElem(e, self)
        self.bin_op = bin_op
        if parent==None:
            self.parent=self
        else:
            self.parent=parent

    def __iter__(self):
        """Iterate over the GroupElems in G, returning the identity first"""
        yield self.e
        for g in self.group_elems:
            if g != self.e: yield g

    def __contains__(self, item):
        return item in self.group_elems

    def __hash__(self):
        return hash(self.Set) ^ hash(self.bin_op)

    def __eq__(self, other):
        if not isinstance(other, Group):
            return False

        return id(self) == id(other) or \
               (self.Set == other.Set and self.bin_op == other.bin_op)

    def __call__(self,el):
        return GroupElem(el,self)

    def __ne__(self, other):
        return not self == other

    def __len__(self):
        return len(self.Set)

    def __str__(self):
        return "Group with "+str(len(self))+" elements"

    def __repr__(self):
        return "Group with "+str(len(self))+" elements"

    def table(self, rep=None):
        """
        Prints the Cayley table
        If rep is "letters" or in text console, will display the table assigning letters to the elemnts in the group
        """

        letters = "eabcdfghijklmnopqrstuvwxyz"
        if len(self) > len(letters):
            return "This group is too big to print a Cayley table"

        # connect letters to elements
        if rep=="letters":
            letters = "eabcdfghijklmnopqrstuvwxyz"
        else:
            letters=[repr(g) for g in self]
        colors = ['Red','Yellow','Lime','Blue','Tan','YellowGreen','Violet','SkyBlue','Tomato',
        'Plum','PaleGreen','Magenta','Mocassin','LightPink', 'LightCyan','Khaki','Ivory','Gray','Fuchsia',
       'Green','Coral','Bisque','Aqua','Azure','DeepPink','Gainsboro','HotPink']

        # connect letters to elements
        toletter = {}
        toelem = {}
        for letter, elem in zip(letters, self):
            toletter[elem] = letter
            toelem[letter] = elem
        letters = letters[:len(self)]
        tocletter = {}
        tocolor = {}
        for letter, color in zip(letters,colors):
            tocolor[letter] = color
            tocletter[color] = letter
        colors = colors[:len(self)]
        try:
            __IPYTHON__
            from IPython.display import display, HTML
            style="<head><style>\ntable, th, td {border: 1px solid black;\n border-collapse: collapse;}\n th, td {padding: 15px;}</style></head>"
            if rep=="letters":
                result =style+ " ".join("%s = %s &nbsp; \n" % (l, toelem[l]) for l in letters)
            else:
                result = style
            # Make the table
            head = "<p/>\n <table>"
            head = head+ "\n <tr> <td bgcolor='White'> * </td> " + " ".join("<td bgcolor="+tocolor[l]+">"+l+"</td>" for l in letters) + " </tr>\n"
            border = "\n "
            result += head
            result += border.join("<tr> <td bgcolor="+str(tocolor[l])+"> %s  </td> " % l + \
                                  "  ".join("<td bgcolor="+tocolor[toletter[toelem[l] * toelem[l1]]]+">"+toletter[toelem[l] * toelem[l1]]+"</td>" \
                                             for l1 in letters) + \
                                  "</tr>" for l in letters)
            result += "\n </table>"

            display(HTML(result))# this won't adjust the height correctly but displays better: metadata=dict(isolated=True))

        except NameError:
            # Display the mapping:
            letters = "eabcdfghijklmnopqrstuvwxyz"
            letters = letters[:len(self)]
            toletter = {}
            toelem = {}
            for letter, elem in zip(letters, self):
                toletter[elem] = letter
                toelem[letter] = elem
            result = "\n".join("%s: %s" % (l, toelem[l]) for l in letters) + "\n\n"

            # Make the graph
            head = "   | " + " | ".join(l for l in letters) + " |"
            border = (len(self) + 1) * "---+" + "\n"
            result += head + "\n" + border
            result += border.join(" %s | " % l + \
                                  " | ".join(toletter[toelem[l] * toelem[l1]] \
                                             for l1 in letters) + \
                                  " |\n" for l in letters)
            result += border
            print(result)


    def is_abelian(self):
        """Checks if the group is abelian"""
        return self.abelian

    def __le__(self, other):
        """Checks if self is a subgroup of other"""
        if not isinstance(other, Group):
            raise TypeError("other must be a Group")
        if self.parent==other:
            return True
        if self.parent==other.parent:
            return self.Set <= other.Set
        return self.Set <= other.Set and \
               all(self.bin_op((a, b)) == other.bin_op((a, b)) \
                   for a in self.Set for b in self.Set)

    def is_normal_subgroup(self, other):
        """Checks if self is a normal subgroup of other"""
        if not(self<=other):
            return False
        if other.is_abelian():
            return True
        return all(Set(g * h for h in self) == Set(h * g for h in self) \
                   for g in other)

    def __truediv__(self, other):
        """ Returns the quotient group self / other """
        if not other.is_normal_subgroup(self):
            raise ValueError("other must be a normal subgroup of self")
        G = Set(Set(self.bin_op((g, h)) for h in other.Set) for g in self.Set)

        def multiply_cosets(x):
            h = x[0].pick()
            return Set(self.bin_op((h, g)) for g in x[1])

        return Group(G, Function(G.cartesian(G), G, multiply_cosets, check_well_defined=False))

    def __div__(self, other):
        """ Returns the quotient group self / other """
        if not other.is_normal_subgroup(self):
            raise ValueError("other must be a normal subgroup of self")
        G = Set(Set(self.bin_op((g, h)) for h in other.Set) for g in self.Set)

        def multiply_cosets(x):
            h = x[0].pick()
            return Set(self.bin_op((h, g)) for g in x[1])

        return Group(G, Function(G.cartesian(G), G, multiply_cosets, check_well_defined=False))

    def inverse(self, g):
        """Returns the inverse of elem"""
        if not g in self.group_elems:
            raise TypeError("g isn't a GroupElem in the Group")
        for a in self:
            if g * a == self.e:
                return a
        raise RuntimeError("Didn't find an inverse for g")

    def __mul__(self, other):
        """
        Computes the product of self and other;
        other can be a group element and we get the lateral class
        """
        if isinstance(other,GroupElem):
            return set([g*other for g in self])
        if self.parent != other.parent:
            raise TypeError("self and other must be subgroups of the same Group")
        gens=Set(self.generators())
        geno=Set(other.generators())
        c=[p[0]*p[1] for p in gens.cartesian(geno)]
        return (self.parent).generate(c)

    def cartesian(self, other):
        """
        Returns the cartesian product of the two groups
        """
        if not isinstance(other, Group):
            raise TypeError("other must be a group")
        bin_op = Function(((self.Set).cartesian(other.Set)).cartesian((self.Set).cartesian(other.Set)), \
                             self.Set.cartesian(other.Set), \
                             lambda x: (self.bin_op((x[0][0], x[1][0])), \
                                        other.bin_op((x[0][1], x[1][1]))), check_well_defined=False)
        ab=False
        if self.is_abelian() and other.is_abelian():
            ab=True
        return Group((self.Set).cartesian(other.Set), bin_op, check_ass=False, check_inv=False, identity=(self.e.elem, other.e.elem),abelian=ab)

    def generate(self, elems):
        """
        Returns the subgroup of self generated by GroupElems elems

        If any of the items aren't already GroupElems, we will try to convert
        them to GroupElems before continuing.

        elems must be iterable
        """

        elems = Set(g if isinstance(g, GroupElem) else GroupElem(g, self) \
                    for g in elems)

        if not elems <= self.group_elems:
            raise ValueError("elems must be a subset of self.group_elems")
        if len(elems) == 0:
            raise ValueError("elems must have at least one element")

        oldG = elems
        while True:
            newG = oldG | Set(a * b for a in oldG for b in oldG)
            if oldG == newG: break
            else: oldG = newG
        oldG = Set(g.elem for g in oldG)
        return Group(oldG, self.bin_op.new_domains(oldG.cartesian(oldG), oldG, check_well_defined=False),parent=self.parent,check_ass=False,check_inv=False, identity=self.e.elem)
    def is_cyclic(self):
        """Checks if self is a cyclic Group"""
        return any(g.order() == len(self) for g in self)

    def subgroups(self):
        """Returns the Set of self's subgroups"""

        old_sgs = Set([self.generate([self.e])])
        while True:
            new_sgs = old_sgs | Set(self.generate(list(sg.group_elems) + [g]) \
                                     for sg in old_sgs for g in self \
                                     if g not in sg.group_elems)
            if new_sgs == old_sgs: break
            else: old_sgs = new_sgs

        n=len(self)
        layers={n:set([self])}
        for i in range(1,n):
            if n%i==0:
                ls=set([H for H in old_sgs if len(H)==i])
                if len(ls)>0:
                    layers.update({i:ls})
        return layers

    def generators(self):
        """
        Returns a list of GroupElems that generate self, with length
        at most log_2(len(self)) + 1
        """

        result = [self.e.elem]
        H = self.generate(result)

        while len(H) < len(self):
            result.append(next(iter(self.Set - H.Set)))
            H = self.generate(result)

        # The identity is always a redundant generator in nontrivial Groups
        if len(self) != 1:
            result = result[1:]

        return [GroupElem(g, self) for g in result]

    def find_isomorphism(self, other):
        """
        Returns an isomorphic GroupHomomorphism between self and other,
        or None if self and other are not isomorphic

        Uses Tarjan's algorithm, running in O(n^(log n + O(1))) time, but
        runs a lot faster than that if the group has a small generating set.
        """
        if not isinstance(other, Group):
            raise TypeError("other must be a Group")

        if len(self) != len(other) or self.is_abelian() != other.is_abelian():
            return None

        # Try to match the generators of self with some subset of other
        A = self.generators()
        for B in itertools.permutations(other, len(A)):

            func = dict(zip(A, B)) # the mapping
            counterexample = False
            while not counterexample:

                # Loop through the mapped elements so far, trying to extend the
                # mapping or else find a counterexample
                noobs = {}
                for g, h in itertools.product(func, func):
                    if g * h in func:
                        if func[g] * func[h] != func[g * h]:
                            counterexample = True
                            break
                    else:
                        noobs[g * h] = func[g] * func[h]

                # If we've mapped all the elements of self, then it's a
                # homomorphism provided we haven't seen any counterexamples.
                if len(func) == len(self):
                    break

                # Make sure there aren't any collisions before updating
                imagelen = len(set(noobs.values()) | set(func.values()))
                if imagelen != len(noobs) + len(func):
                    counterexample = True
                func.update(noobs)

            if not counterexample:
                return GroupHomomorphism(self, other, lambda x: func[x])

        return None

    def is_isomorphic(self, other):
        """Checks if self and other are isomorphic"""
        return bool(self.find_isomorphism(other))

    def intersection(self, other):
        """
        Computes the intersection of self and other
        """
        if self.parent==None or other.parent==None:
            raise TypeError("self and other must be subgroups of the same Group")
        if self.parent != other.parent:
            raise TypeError("self and other must be subgroups of the same Group")
        common = Set(self.Set & other.Set)
        return Group(common,Function(common.cartesian(common), common, self.bin_op,check_well_defined=False),self.parent,check_ass=False,check_inv=False,identity=self.e.elem)

    def conjugacy_classes(self):
        """Compute the set of conjugacy clases of the elements of a group; see conjugacy_class of a group element"""
        cls=set([])
        G=list(self.group_elems)
        while len(G)>1:
            x=G[0]
            H=x.conjugacy_class()
            cls.add(H)
            G=[g for g in G if not(g in H)]
        return cls

    def center(self):
        """Computes the center of self: the subgroup of element g such that g*h=h*g for all h in G"""
        G=Set([g.elem for g in self if all(g*h==h*g for h in self)])
        op=self.bin_op.new_domains(G.cartesian(G),G,check_well_defined=False)
        return Group(G,op,parent=self.parent, check_ass=False, check_inv=False, abelian=True,identity=self.e.elem)

    def conjugacy_class(self):
        """Computes the set of g*self*g^-1 for all g in self.parent"""
        cls=set([])
        G=list(self.parent.group_elems)
        H=list(self.group_elems)
        for g in G:
            N=frozenset([g*h*g**-1 for h in H])
            cls.add(N)
        return cls

    def normalizer(self):
        """Computes the normalizer of self in self.parent"""
        if self.Set==self.parent.Set:
            return self
        G=list(self.parent.group_elems)
        H=list(self.group_elems)
        N=Set([g.elem for g in G if set([g*h for h in H])==set([h*g for h in H])])
        op=self.bin_op.new_domains(N.cartesian(N),N,check_well_defined=False)
        return Group(N,op,parent=self.parent, check_ass=False, check_inv=False, identity=self.e.elem)

class GroupHomomorphism(Function): #we should add here check_well_defined, and check_group_axioms as options
    """
    The definition of a Group Homomorphism

    A GroupHomomorphism is a Function between Groups that obeys the group
    homomorphism axioms.
    """

    def __init__(self, domain, codomain, function):
        """Check types and the homomorphism axioms; records the two groups"""

        if not isinstance(domain, Group):
            raise TypeError("domain must be a Group")
        if not isinstance(codomain, Group):
            raise TypeError("codomain must be a Group")
        if not all(function(elem) in codomain for elem in domain):
            raise TypeError("Function returns some value outside of codomain")

        if not all(function(a * b) == function(a) * function(b) \
                   for a in domain for b in domain):
            raise ValueError("function doesn't satisfy the homomorphism axioms")

        self.domain = domain
        self.codomain = codomain
        self.function = function

    def kernel(self):
        """Returns the kernel of the homomorphism as a Group object"""
        G = Set(g.elem for g in self.domain if self(g) == self.codomain.e)
        return Group(G, self.domain.bin_op.new_domains(G.cartesian(G), G, check_well_defined=False),parent=self.domain, check_ass=False,check_inv=False,identity=self.domain.e.elem)

    def image(self):
        """Returns the image of the homomorphism as a Group object"""
        G = Set(g.elem for g in self._image())
        return Group(G, self.codomain.bin_op.new_domains(G.cartesian(G), G, check_well_defined=False),parent=self.codomain, check_ass=False,check_inv=False,identity=self.codomain.e.elem)

    def is_isomorphism(self):
        return self.is_bijective()


def CyclicGroup(n, rep="integers"):
    """
    Returns the cylic group of order n

    Args:
        n a positive integer
        rep may be either "integers" and then the output is integers mod n, or "permuations" and the output is the subgroup of S_n generated by the cycle (1..n)

    Example:
        >>> CP=CyclicGroup(3,"permutations")
        >>> CP.Set
        Set([ (1, 2, 3),  (1, 3, 2), ( )])
        >>> C=CyclicGroup(3,"integers")
        >>> C.group_elems
        Set([0, 1, 2])
        >>> CP.is_isomorphic(C)
        True
    """
    if rep=="integers":
        G = Set(range(n))
        bin_op = Function(G.cartesian(G), G, lambda x: (x[0] + x[1]) % n)
        return Group(G, bin_op,check_ass=False,check_inv=False,identity=0,abelian=True)
    if rep=="permutations":
        G=SymmetricGroup(n)
        c=G(permutation(tuple([i+1 for i in range(n)])))
        return G.generate([c])
    raise ValueError("The second argument can be 'integers' or 'permutations'")

def SymmetricGroup(n):
    """
    Returns the symmetric group of order n!

    Example:
        >>> S3=SymmetricGroup(3)
        >>> S3.group_elems
        Set([ (2, 3),  (1, 3),  (1, 2),  (1, 3, 2), ( ),  (1, 2, 3)])
    """
    G = Set(permutation(list(g)) for g in itertools.permutations(list(range(1,n+1))))
    bin_op = Function(G.cartesian(G), G, lambda x: x[0]*x[1])
    if n>2:
        return Group(G, bin_op,check_ass=False,check_inv=False,identity=tuple(range(n)),abelian=False)
    return Group(G, bin_op,check_ass=False,check_inv=False,identity=tuple(range(n)),abelian=True)


def AlternatingGroup(n):
    """
    Returns the alternating group: the subgroup of even permutations of SymmetricGroup(n)

    Example:
        >>> A3=AlternatingGroup(3)
        >>> A3<=S3
        True
        >>> A3.is_normal_subgroup(S3)
        True
        >>> Q=S3/A3
        >>> Q.Set
        Set([Set([ (2, 3),  (1, 2),  (1, 3)]), Set([ (1, 2, 3),  (1, 3, 2), ( )])])
    """
    G = Set(permutation(list(g)) for g in itertools.permutations(list(range(1,n+1))) if permutation(list(g)).sign()==1)
    bin_op = Function(G.cartesian(G), G, lambda x: x[0]*x[1])
    if n>2:
        return Group(G, bin_op,check_ass=False,check_inv=False,identity=tuple(range(n)),abelian=False,parent=SymmetricGroup(n))
    return Group(G, bin_op,check_ass=False,check_inv=False,identity=tuple(range(n)),abelian=True,parent=SymmetricGroup(n))



def DihedralGroup(n, rep="RS"):
    """
    Returns the dihedral group of order 2n

    Args:
        n is a positive integer
        rep can be "RS" if we want rotations and symmtries, or "permutations" if we want to see DihedralGroup(n) inside SymmetricGroup(n)

    Example:
        >>> D3=DihedralGroup(3)
        >>> DP3=DihedralGroup(3,"permutations")
        >>> D3.is_isomorphic(DP3)
        True
        >>> D3.Set
        Set(['R0', 'R1', 'R2', 'S2', 'S1', 'S0'])
        >>> DP3.Set
        Set([ (2, 3),  (1, 3),  (1, 2),  (1, 3, 2), ( ),  (1, 2, 3)])
    """
    if rep=="RS":
        G = Set("%s%d" % (l, x) for l in "RS" for x in range(n))
        def multiply_symmetries(x):
            l1, l2 = x[0][0], x[1][0]
            x1, x2 = int(x[0][1:]), int(x[1][1:])
            if l1 == "R":
                if l2 == "R":
                    return "R%d" % ((x1 + x2) % n)
                else:
                    return "S%d" % ((x1 + x2) % n)
            else:
                if l2 == "R":
                    return "S%d" % ((x1 - x2) % n)
                else:
                    return "R%d" % ((x1 - x2) % n)
        return Group(G, Function(G.cartesian(G), G, multiply_symmetries))
    if rep=="permutations":
        G=SymmetricGroup(n)
        r=G(permutation(tuple([i+1 for i in range(n)])))
        s=G(permutation([(i+1,n-i) for i in range(n//2)]))
        return G.generate([r,s])
    raise ValueError("The second argument can be 'RS' or 'permutations'")

def QuaternionGroup():
    """
    The quaternion group Q2; its elments are 1,i,j,k and their oposite

    Example:
        >>> Q2=QuaternionGroup()
        >>> list(Q2)
        ['1', 'i', 'k', 'j', '-i', '-k', '-j', '-1']
        >>> i=Q2("i")
        >>> j=Q2("j")
        >>> i*j
        'k'
        >>> j*i
        '-k'
    """
    q2=[ "1", "-1", "i", "-i", "j", "-j", "k", "-k"]
    table=[[ "1", "-1", "i", "-i", "j", "-j", "k", "-k"],[ "-1", "1", "-i", "i", "-j", "j", "-k", "k"],[ "i", "-i", "-1", "1", "k", "-k", "-j", "j"],[ "-i", "i", "1", "-1", "-k", "k", "j", "-j"],[ "j", "-j", "-k", "k", "-1", "1", "i", "-i"],[ "-j", "j", "k", "-k", "1", "-1", "-i", "i"],[ "k", "-k", "j", "-j", "-i", "i", "-1", "1"],[ "-k", "k", "-j", "j", "i", "-i", "1", "-1"]]
    def product(a,b):
        i=q2.index(a)
        j=q2.index(b)
        return table[i][j]
    G=Set(q2)
    return Group(G,Function(G.cartesian(G),G, lambda x: product(x[0],x[1])))

def KleinGroup(rep="integers"):
    """
    The Klein four-group; it can be represented via "integers" as Z_2 x Z_2, and as a subgroup of permutations of A_4

    Example:
        >>> K=KleinGroup()
        >>> KK=KleinGroup("permutations")
        >>> KK.is_isomorphic(K)
        True
        >>> list(K)
        [(0, 0), (0, 1), (1, 0), (1, 1)]
        >>> list(KK)
        [( ),  (1, 4)(2, 3),  (1, 3)(2, 4),  (1, 2)(3, 4)]
    """
    if rep=="integers":
        G=CyclicGroup(2)
        return G.cartesian(G)
    if rep=="permutations":
        G=AlternatingGroup(4)
        return G.generate([permutation((1,2),(3,4)), permutation((1,3),(2,4))])
    raise ValueError("The second argument can be 'RS' or 'permutations'")


def GroupOfUnitsModInt(n):
    G=Set([m for m in range(n) if gcd(n,m)==1])
    bop=Function(G.cartesian(G),G,lambda x: (x[0]*x[1])%n,check_well_defined=False)
    return Group(G,bop, check_inv=False, check_ass=False, abelian=True, identity=1)

class permutation:
    """
    This is the class of permutations of the set {1..n}

    Attributes:
        tuple: a tuple of n integers that stores the images of 1..n under the permutation
        length: n with the above notation
    """
    def __init__(self,*els):
        """
        Defines a permutation

        Args:
            *els: can be a list of integers or a list of tuples integers or a sequence of integers or a sequence of tuples of integers

        Returns:
            A permutation.
            If a list or sequence of integers is given, then the output is the permutation that sends 1 to the firs element in the list or sequence, 2 to the second, and so on.
            If a list or sequence of tuples is given, then they are considered as cycles, and the output is the product of these cycles.

        Example:
            >>> p=permutation([2,1,4,3])
            >>> q=permutation((1,2),(3,4))
            >>> p==q
            True
            >>> p=permutation(2,1,4,3)
            >>> p==q
            True

        """
        def cycle2perm(c):
            """Returns a permuation corresponding to the cycle given by the tuple c"""
            m=len(c)
            if len==0: #this will not happen
                return tuple([1])
            n=max(c)
            p=[i+1 for i in range(n)]
            for i in range(1,n+1):
                if (i in c):
                    p[i-1]=c[(c.index(i)+1)%m]
            return permutation(p)
        if len(els)==1:
            t=els[0]
        else:
            t=list(els)
        if not(isinstance(t,list)) and not(isinstance(t,tuple)):
            raise TypeError("expecting a list or sequence of integers or tuples of integers as argument")
        n=len(t)
        if n==0:
            raise TypeError("to avoid ambiguity empty permutations are not allowed")
        if all(isinstance(x,int) for x in t) and isinstance(t,list):
            if set(t)!=set(range(1,n+1)):
                raise TypeError("the input is not a permutation of "+str(range(1,n+1)))
            self.tuple=tuple(t)
            self.length=n
        elif all(isinstance(x,int) for x in t) and isinstance(t,tuple):
            p=cycle2perm(t)
            self.tuple=p.tuple
            self.length=p.length
        elif all(isinstance(x,tuple) for x in t):
            cs=[cycle2perm(c) for c in t]
            p=functools.reduce(operator.mul,cs)
            self.tuple=p.tuple
            self.length=p.length
        else:
            raise TypeError("expecting a list or sequence of integers or tuples of integers as argument")

    def __hash__(self):
        return hash(self.tuple)

    def __str__(self):
        s=str(list(self.tuple))+" = "
        cs=self.disjoint_cycles()
        s2=str(" ")
        for c in cs:
            if len(c)>1:
                s2=s2+str(c)
        if s2==str(" "):
            return s+"( )"
        return s+s2

    def __repr__(self):
        cs=self.disjoint_cycles()
        s2=str(" ")
        for c in cs:
            if len(c)>1:
                s2=s2+str(c)
        if s2==str(" "):
            return "( )"
        return s2

    def __eq__(self, other):
        """Tests if the permutations are identical (with the same length)"""

        if not isinstance(other, permutation):
            raise TypeError("other is not a permutation")
        return (self.tuple == other.tuple)

    def __ne__(self, other):
        return not self == other

    def __mul__(self,other):
        """
        Composition of permutations

        Example:
            >>> p=permutation((1,3))
            >>> q=permutation([2,1,3])
            >>> p*q
             (1, 2, 3)
        """
        if not(isinstance(other,permutation)):
            raise TypeError("other must also be a permutation")
        p=list(self.tuple)
        q=list(other.tuple)
        n=len(p)
        m=len(q)
        mx=max([n,m])
        if n>m:
            q=q+list(range(m+1,n+1))
        if m>n:
            p=p+list(range(n+1,m+1))
        o=[p[q[i-1]-1] for i in range(1,mx+1)]
        return permutation(o)

    def inverse(self):
        """
        Inverse of a permuatation (as a function)

        Example:
            >>> q=permutation([2,3,1])
            >>> q
             (1, 2, 3)
            >>> q**-1
             (1, 3, 2)
        """
        l=list(self.tuple)
        n=len(l)
        p=[l.index(i)+1 for i in range(1,n+1)]
        return permutation(p)

    def __pow__(self, n):
        """
        Returns the composition of a permutation n times

        Example:
            >>> q=permutation([2,3,1])
            >>> q**3
            ( )
            >>> q*q==q**2
            True
        """
        if not (isinstance(n, int)):
            raise TypeError("n must be an int or a long")

        k=self.length
        if n == 0:
            return permutation(list(range(1,k+1)))
        elif n < 0:
            return self.inverse() ** -n
        elif n % 2 == 1:
            return self * (self ** (n - 1))
        else:
            return (self * self) ** (n // 2)

    def disjoint_cycles(self):
        """
        Returns a list of disjoint cycles (as tuples) whose product is the given permutation (argument)

        Example:
            >>> p=permutation([2,1,4,3])
            >>> p.disjoint_cycles()
            [(1, 2), (3, 4)]
        """
        l=[]
        p=list(self.tuple)
        els=set(p)
        while len(els)>0:
            e=next(iter(els))
            c=[e]
            while not(p[e-1] in c):
                e=p[e-1]
                c.append(e)
            l.append(tuple(c))
            els=[a for a in els if not(a in c)]
        return l #[c for c in l if len(c.tuple)>1]

    def inversions(self):
        """
        List of inversions of the given permutation p, that is, the set of pairs (i,j) in {1..n}^2 with i<j such that p(i)>p(j)

        Example:
            >>> q=permutation([2,3,1])
            >>> q.inversions()
            [(1, 3), (2, 3)]
        """
        p=list(self.tuple)
        n=len(p)
        return [tuple([i,j]) for i in range(1,n+1) for j in range(i+1,n+1) if p[i-1]>p[j-1]]

    def sign(self):
        """
        The sign of the permuation, that is, (-1)^i, with i the number of inversions of the permutation
        Example:
            >>> q=permutation([2,3,1])
            >>> q.inversions()
            [(1, 3), (2, 3)]
            >>> q.sign()
            1
        """
        return (-1)**len(self.inversions())

    def order(self):
        """
        The order of the permutation, that is, minimum positive integer such that p**n==identity, with p the argument
        Example:
            >>> p=permutation([4,3,1,2])
            >>> p.order()
            4
        """
        l=[len(c) for c in self.disjoint_cycles()]
        if len(l)==1:
            return l[0]
        return (functools.reduce(operator.mul,l))//(functools.reduce(gcd,l))
