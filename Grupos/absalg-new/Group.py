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
        Two GroupElems are equal if they represent the same element,
        regardless of the Groups they belong to
        """

        if not isinstance(other, GroupElem):
            raise TypeError("other is not a GroupElem")
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
            return GroupElem(self.group.bin_op((self.elem, other.elem)), \
                             self.group)
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
        return frozenset([g*self*g**-1 for g in self.group])

    def centralizer(self):
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

    def table(self):
        """Prints the Cayley table"""

        letters = "eabcdfghijklmnopqrstuvwxyz"
        if len(self) > len(letters):
            return "This group is too big to print a Cayley table"

        # connect letters to elements
        letters = "eabcdfghijklmnopqrstuvwxyz"
        colors = ['Red','Yellow','Lime','Blue','Tan','YellowGreen','Violet','SkyBlue','Tomato',
        'Plum','PaleGreen','Magenta','Mocassin','LightPink', 'LightCyan','Khaki','Ivory','Gray','Fuchsia',
       'Green','Coral','Bisque','Aqua','Azure','DeepPink','Gainsboro','HotPink']
        if len(self) > len(letters):
            return "This group is too big to print a Cayley table"

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
            result =style+ " ".join("%s = %s <p/>\n" % (l, toelem[l]) for l in letters)

            # Make the graph
            head = "<p/>\n <table>"
            head = head+ "\n <tr> <td bgcolor='White'> * </td> " + " ".join("<td bgcolor="+tocolor[l]+">"+l+"</td>" for l in letters) + " </tr>\n"
            border = "\n "
            result += head
            result += border.join("<tr> <td bgcolor="+str(tocolor[l])+"> %s  </td> " % l + \
                                  "  ".join("<td bgcolor="+tocolor[toletter[toelem[l] * toelem[l1]]]+">"+toletter[toelem[l] * toelem[l1]]+"</td>" \
                                             for l1 in letters) + \
                                  "</tr>" for l in letters)
            result += "\n </table>"

            display(HTML(result),metadata=dict(isolated=True))

        except NameError:
            # Display the mapping:
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

        return Group(G, Function(G.cartesian(G), G, multiply_cosets))

    def __div__(self, other):
        """ Returns the quotient group self / other """
        if not other.is_normal_subgroup(self):
            raise ValueError("other must be a normal subgroup of self")
        G = Set(Set(self.bin_op((g, h)) for h in other.Set) for g in self.Set)

        def multiply_cosets(x):
            h = x[0].pick()
            return Set(self.bin_op((h, g)) for g in x[1])

        return Group(G, Function(G.cartesian(G), G, multiply_cosets))

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
        """Returns the cartesian product of the two groups"""
        if not isinstance(other, Group):
            raise TypeError("other must be a group")
        bin_op = Function(((self.Set).cartesian(other.Set)).cartesian((self.Set).cartesian(other.Set)), \
                             self.Set.cartesian(other.Set), \
                             lambda x: (self.bin_op((x[0][0], x[1][0])), \
                                        other.bin_op((x[0][1], x[1][1]))))
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
        if self.parent==None:
            return Group(oldG, self.bin_op.new_domains(oldG.cartesian(oldG), oldG),self)
        return Group(oldG, self.bin_op.new_domains(oldG.cartesian(oldG), oldG),parent=self.parent,check_ass=False,check_inv=False, identity=self.e.elem, abelian=self.abelian)
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

        return old_sgs

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

            func = dict(itertools.izip(A, B)) # the mapping
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
        """Computes the intersection of self and other"""
        if self.parent==None or other.parent==None:
            raise TypeError("self and other must be subgroups of the same Group")
        if self.parent != other.parent:
            raise TypeError("self and other must be subgroups of the same Group")
        common = Set(self.Set & other.Set)
        return Group(common,Function(common.cartesian(common), common, self.bin_op),self.parent,check_ass=False,check_inv=False,identity=self.e.elem)

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
        op=self.bin_op.new_domains(G.cartesian(G),G)
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
        op=self.bin_op.new_domains(N.cartesian(N),N)
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
        return Group(G, self.domain.bin_op.new_domains(G.cartesian(G), G),check_ass=False,check_inv=False,identity=self.domain.e.elem)

    def image(self):
        """Returns the image of the homomorphism as a Group object"""
        G = Set(g.elem for g in self._image())
        return Group(G, self.codomain.bin_op.new_domains(G.cartesian(G), G),check_ass=False,check_inv=False,identity=self.codomain.e.elem)

    def is_isomorphism(self):
        return self.is_bijective()


def Zn(n):
    """Returns the cylic group of order n"""
    G = Set(range(n))
    bin_op = Function(G.cartesian(G), G, lambda x: (x[0] + x[1]) % n)
    return Group(G, bin_op,check_ass=False,check_inv=False,identity=0,abelian=True)

def Sn(n):
    """Returns the symmetric group of order n! """
    G = Set(g for g in itertools.permutations(list(range(1,n+1))))
    bin_op = Function(G.cartesian(G), G, lambda x: tuple(x[0][j-1] for j in x[1]))
    if n>2:
        return Group(G, bin_op,check_ass=False,check_inv=False,identity=tuple(range(n)),abelian=False)
    return Group(G, bin_op,check_ass=False,check_inv=False,identity=tuple(range(n)),abelian=True)

def SymmetricGroup(n):
    """Returns the symmetric group of order n! """
    G = Set(permutation(list(g)) for g in itertools.permutations(list(range(1,n+1))))
    bin_op = Function(G.cartesian(G), G, lambda x: x[0]*x[1])
    if n>2:
        return Group(G, bin_op,check_ass=False,check_inv=False,identity=tuple(range(n)),abelian=False)
    return Group(G, bin_op,check_ass=False,check_inv=False,identity=tuple(range(n)),abelian=True)

def An(n):
    """Returns the alternating group: the subgroup of even permutations of Sn(n)"""
    G = Set(g for g in itertools.permutations(list(range(1,n+1))) if permutation(list(g)).sign()==1)
    bin_op = Function(G.cartesian(G), G, lambda x: tuple(x[0][j-1] for j in x[1]))
    if n>2:
        return Group(G, bin_op,check_ass=False,check_inv=False,identity=tuple(range(n)),abelian=False,parent=Sn(n))
    return Group(G, bin_op,check_ass=False,check_inv=False,identity=tuple(range(n)),abelian=True,parent=Sn(n))


def Dn(n):
    """Returns the dihedral group of order 2n """
    G = Set("%s%d" % (l, x) for l in "RS" for x in xrange(n))
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

class permutation:
    """Defines a permutation from a tuple of images"""
    def __init__(self,*els):
        def cycle2perm(c):
            """Returns a tuple that represents the (permutation) cycle given by c """
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
        """
        Two GroupElems are equal if they represent the same element,
        regardless of the Groups they belong to
        """

        if not isinstance(other, permutation):
            raise TypeError("other is not a permutation")
        return (self.tuple == other.tuple)

    def __ne__(self, other):
        return not self == other

    def __mul__(self,other):
        """Composition of other and self"""
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
        """Inverse of self"""
        l=list(self.tuple)
        n=len(l)
        p=[l.index(i)+1 for i in range(1,n+1)]
        return permutation(p)

    def __pow__(self, n):
        """
        Returns self**n
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
        """Returns a list of disjoint cycles (as tuples) whose product is self"""
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
        """List of inversions of self"""
        p=list(self.tuple)
        n=len(p)
        return [tuple([i,j]) for i in range(1,n+1) for j in range(i+1,n+1) if p[i-1]>p[j-1]]

    def sign(self):
        """The sign of self"""
        return (-1)**len(self.inversions())

    def order(self):
        """The order of self, that is, min n such that self**n=identity"""
        l=[len(c) for c in self.disjoint_cycles()]
        return (functools.reduce(operator.mul,l))//(functools.reduce(gcd,l))

    def as_GroupElem(self):
        return GroupElem(self.tuple,Sn(self.length))
