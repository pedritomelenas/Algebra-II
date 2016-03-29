"""Group implementation"""

import itertools
import functools
import operator
import math
from Set import Set
from Function import Function
from fractions import gcd
from copy import deepcopy
from sympy.ntheory import factorint,totient
from sympy.utilities.iterables import flatten

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

        if isinstance(other,Group):
            return Set(self.group.bin_op((self.elem, h)) for h in other.Set)
        #if isinstance(other,set):
        #    return set([self*g for g in other])
        if self.group.is_abelian() and isinstance(other, (int)):
            return self ** other

        if not isinstance(other, GroupElem):
            raise TypeError("other must be a GroupElem, or an int " \
                            "(if self's group is abelian)")
        if not(self.group.parent==other.group.parent):
            raise TypeError("both elements must be in the same group")
        #try:
        return GroupElem(self.group.parent.bin_op((self.elem, other.elem)), \
                             self.group.parent)
        # This can return a TypeError in Funcion.__call__ if self and other
        # belong to different Groups. So we see if we can make sense of this
        # operation the other way around.
        #except TypeError:
        #    return other.__rmul__(self)

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

    def conjugate(self,g):
        return g*self*g**-1

    def conjugacy_class(self):
        """
        Returns the conjugacy class of self in self.group
        """
        return frozenset([g*self*g**-1 for g in self.group])

    def centralizer(self):
        """
        Returns the centralizer of self, that is, the set of elements that commute with self
        """
        G=self.group
        def prop(g):
            return g*self  ==  self*g
        return G.subgroup_search(prop)

    def order(self):
        G=self.group
        if not  self in G:
            raise ValueError
        identity = G(G.e.elem)
        if self == identity:
            return 1
        i = 1
        x = self
        while not x == identity:
            x = x*self
            i = i + 1
        return i

class Group:
    """Group definition"""

    def __init__(self, G, bin_op, parent=None, check_ass=True, check_inv=True, identity=None, abelian=None, group_order=None, group_degree=None):
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

        # Test associativity
        if check_ass:
            if not all(bin_op((a, bin_op((b, c)))) == \
                       bin_op((bin_op((a, b)), c)) \
                       for a in G for b in G for c in G):
                raise ValueError("binary operation is not associative")

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
        self.group_gens=list(self.group_elems)
        self.group_order=group_order
        self.group_degree=group_degree

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
        if self.group_gens!=None:
            gs = "Group( "+str(self.group_gens)+" )"
            if len(gs)>100:
                gs = "Group with "+str(len(self))+" elements"
        else:
            gs = "Group with "+str(len(self))+" elements"
        return gs

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
        return self.is_subgroup(other)

    def is_subgroup(self, other):
        """Return True if all elements of self belong to other.
        """
        if not isinstance(other, Group):
           return False
        if self == other:
            return True
        if self.parent==other:
            return True
        if other.order() % self.order() != 0:
            return False
        gens = self.group_gens
        return Set(self.group_gens)<=Set(other.group_elems) and \
            all(self.bin_op((a.elem, b.elem)) == other.bin_op((a.elem, b.elem)) for a in self.group_gens for b in self.group_gens)

    def is_normal_subgroup(self, other):
        """Checks if self is a normal subgroup of other"""
        if not(self<=other):
            return False
        if other.is_abelian():
            return True
        gens1 = self.group_gens
        gens2 = other.group_gens
        for g in gens2:
            for h in gens1:
                p = g * h * g**-1
                if not p in Set(self.group_elems):
                    return False
        return True


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
            return Set(other.group.bin_op((h, other.elem)) for h in self.Set)
            #return set([g*other for g in self])
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
        Gr=Group((self.Set).cartesian(other.Set), bin_op, check_ass=False, check_inv=False, identity=(self.e.elem, other.e.elem),abelian=ab,group_order=self.group_order*other.group_order)
        Gr.group_gens=[(self.e.elem,b)  for b in other.group_gens]+[(a,other.e.elem)  for a in self.group_gens]
        return Gr

    def subgroup_by_elms(self, elems):
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

        if not(all(f*g in self for f in elems for g in elems)):
            raise ValueError("the set elems is not closed under the operation")

        G=Set([el.elem for  el in elems])
        op=self.bin_op.new_domains(G.cartesian(G),G,check_well_defined=False)
        Gr=Group(G,op,parent=self.parent, check_ass=False, check_inv=False,identity=self.e.elem,group_order=len(elems))
        Gr.group_gens=elems
        return Gr

    def generate(self,generators):
        """
        Returns the subgroup of self generated by the list generators of GroupElems

        If any of the items aren't already GroupElems, we will try to convert
        them to GroupElems before continuing.

        generators must be iterable
        """
        idn = self(self.e.elem)
        ord = 1
        element_list = [idn]
        set_element_list = set([idn])
        gens = [g if isinstance(g, GroupElem) else GroupElem(g, self) for g in generators]
        for i in range(len(gens)):
            # D elements of the subgroup G_i generated by gens[:i]
            D = element_list[:]
            N = [idn]
            while N:
                A = N
                N = []
                for a in A:
                    for g in gens[:i + 1]:
                        ag = a*g
                        if ag not in set_element_list:
                        # produce G_i*g
                            for d in D:
                                ord += 1
                                ap = d*ag
                                element_list.append(ap)
                                set_element_list.add(ap)
                                N.append(ap)
        oldG = Set(g.elem for g in element_list)
        G=Group(oldG, self.bin_op.new_domains(oldG.cartesian(oldG), oldG, check_well_defined=False),
                     parent=self.parent,check_ass=False,check_inv=False, identity=self.e.elem,group_order=ord)
        G.group_gens=gens
        return G

    def subgroup_search(self, prop):
        """Return a subgroup of all elements satisfying the property."""
        H=set([self(self.e.elem)])
        G=self.group_elems
        F=G-H
        while len(F)>0:
            g=Set(F).pick()
            if prop(g):
                H=set(self.generate(list(H|set([g]))))
                F=F-H
            else:
                Dg=Set([g*h for h in H])
                F=Set(F-Dg)
        oldG = Set(g.elem for g in H)
        G=Group(oldG, self.bin_op.new_domains(oldG.cartesian(oldG), oldG, check_well_defined=False),
                     parent=self.parent,check_ass=False,check_inv=False, identity=self.e.elem,group_order=len(oldG))
        return G

    def element_search(self, prop):
        """Return an element satisfying the property."""
        H=set([self(self.e.elem)])
        G=self.group_elems
        F=G-H
        while len(F)>0:
            g=Set(F).pick()
            if prop(g):
                return g
            else:
                Dg=Set([g*h for h in H])
                F=Set(F-Dg)
        return g

    def normal_closure(self, other):
        """Return the normal closure of other in self."""
        if not(other<=self):
            raise TypeError("The argument must be subgroup of the given group")
        G=self.group_gens
        U=other.group_gens
        N=[]
        for x in U:
            N.append(x)
        for d in N:
            for g in G:
                c=g*d*g**-1
                if not c in self.generate(N):
                    N.append(c)
        return self.generate(N)

    def orders(self):
        """Return the dictionary of the orders of all the elements of self."""
        L=self.group_elems
        orders = {}
        for x in L:
            orders.update({x:x.order()})
        return orders

    def is_cyclic(self):
        """Checks if self is a cyclic Group"""
        return any(g.order() == len(self) for g in self)

    def subgroups(self,k=None):
        """Returns the a dictionay of self's subgroups of the form order:groups of this order"""

        if k==None:
            old_sgs = Set([self.generate([self.e])])
            while True:
                new_sgs = old_sgs | Set(self.generate(list(sg.group_elems) + [g]) \
                                         for sg in old_sgs for g in self \
                                         if g not in sg.group_elems)
                if new_sgs == old_sgs: break
                else: old_sgs = new_sgs

            n=self.order()
            layers={n:set([self])}
            for i in range(1,n):
                if n%i==0:
                    ls=set([H for H in old_sgs if len(H)==i])
                    if len(ls)>0:
                        layers.update({i:ls})
            return layers
        if not(isinstance(k,int)):
            raise ValueError("The second argument, if given, must be an integer")
        if (k<=0) or (len(self)%k!=0):
            return []
        if k==1:
            return self.generate([self.e.elem])
        if k==self.order():
            return self
        elem_e=set([self.e])
        elems=set(self.group_elems)
        L=elems.difference(elem_e)
        K=itertools.combinations(L,k-1)
        K=[set(x) for x in K]
        K=[x.union(elem_e) for x in K]
        return [self.subgroup_by_elms(A) for A in K if all(f*g in A for f in A for g in A)]

    def normal_subgroups(self):
        """Filters the dictionary of subgroups with those that are normal"""
        sbs=self.subgroups()
        nsbs={}
        for i in sbs.keys():
            ls=set([H for H in sbs[i] if H.is_normal_subgroup(self)])
            if len(ls)>0:
                nsbs.update({i:ls})
        return nsbs

    def Sylow_subgroups(self,p):
        n=len(self)
        r=1
        while n%p ==0:
            r=r*p
            n=n/p
        return self.subgroups(r)

    def is_transitive(self):
        f=GroupAction(self,Set(list(range(1,self.group_degree+1))),lambda x,y:x.elem(y))
        return f.is_transitive()

    def order(self):
        """Return the order of the group.
        """
        if self.group_order != None:
            return self.group_order
        self.group_order = len(self)
        return self.group_order

    def index(self,other):
        if not isinstance(self, Group):
            raise TypeError("self is not a Group")
        if other <= self:
            return self.order()//other.order()

    def generators(self):
        """
        Returns a list of GroupElems that generate self, with length
        at most log_2(len(self)) + 1
        """

        if len(self.group_gens) != len(self):
            return self.group_gens
        result = [self.e.elem]
        H = self.generate(result)

        while len(H) < len(self):
            result.append(next(iter(self.Set - H.Set)))
            H = self.generate(result)

        # The identity is always a redundant generator in nontrivial Groups
        if len(self) != 1:
            result = result[1:]

        self.group_gens= [GroupElem(g, self) for g in result]
        return self.group_gens

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
        return Group(common,Function(common.cartesian(common), common, self.bin_op.function, check_well_defined=False), self.parent,check_ass=False,check_inv=False,identity=self.e.elem)

    def conjugacy_classes(self):
        """Compute the set of conjugacy clases of the elements of a group; see conjugacy_class of a group element"""
        cls=set([])
        G=list(self.group_elems)
        while len(G)>0:
            x=G[0]
            H=x.conjugacy_class()
            cls.add(H)
            G=[g for g in G if not(g in H)]
        return cls

    def conjugate_subgroup(self,other,g):
        conj=[g*x*g**-1 for x in other.group_gens]
        return self.generate(conj)

    def conjugacy_class_subgroup(self,other):
        """Computes the set of g*other*g^-1 for all g in self"""
        cls=Set([self.conjugate_subgroup(other,g) for g in self.group_elems])
        return cls

    def conjugacy_classes_subgroups(self):
        """Computes the set of g*H*g^-1 for all H subgroup of self"""
        sbs_d=self.subgroups()
        sbs=[H for j in sbs_d.keys() for H in sbs_d[j]]
        cls=set([self.conjugacy_class_subgroup(H) for H in sbs])
        return cls

    def cosets(self,other,side="left"):
        if not(other<=self):
            raise ValueError("The first argument must be a subgroup of the given group")
        if side=="right":
            cls=[set(other.group_elems)]
            D=list((self.group_elems)-(other.group_elems))
            while len(D)>0:
                a=D[0]
                new=set(a*h for h in other)
                cls.append(new)
                D=list(set(D)-new)
            return cls
        if side=="left":
            cls=[set(other.group_elems)]
            D=list((self.group_elems)-(other.group_elems))
            while len(D)>0:
                a=D[0]
                new=set(h*a for h in other)
                cls.append(new)
                D=list(set(D)-new)
            return cls
        raise ValueError("The second argument must be either 'left' or 'right'")

    def normalizer(self,other):
        S=other.group_gens
        H=other.group_elems
        def prop(g):
            return all((g*h*g**-1 in H) for h in S)
        return self.subgroup_search(prop)

    def is_simple(self):
        """Determines if the group is simple"""
        return len(self.normal_subgroups())==2

    def commutator(self,H,K):
        ggens = H.group_gens
        hgens = K.group_gens
        commutators = []
        for ggen in ggens:
            for hgen in hgens:
                commutator = hgen * ggen * hgen**-1 * ggen**-1
                if commutator not in commutators:
                    commutators.append(commutator)
        res = self.normal_closure(self.generate(commutators))
        return res

    def centralizer(self,other):
        def prop(g):
            return [g*h for h in other.group_gens]  ==  [h*g for h in other.group_gens]
        return self.subgroup_search(prop)

    def center(self):
        """Computes the center of self: the subgroup of element g such that g*h=h*g for all h in G"""
        return self.centralizer(self)

    def derived_subgroup(self):
        """Return the derived subgroup of the group."""
        return self.commutator(self, self)

    def derived_series(self):
        res = [self]
        current = self
        nextgroup = self.derived_subgroup()
        while not current<=nextgroup:
            res.append(nextgroup)
            current = nextgroup
            nextgroup = nextgroup.derived_subgroup()
        return res

    def is_trivial(self):
        return self.order== 1 and all(g.elem == self.e.elem for g in self)

    def is_soluble(self):
        ds = self.derived_series()
        terminator = ds[len(ds) - 1]
        return terminator.is_trivial()

    def group_lattice(self):
        from graphviz import Digraph
        from IPython.display import display, Image,HTML
        G=Digraph(graph_attr={'rankdir': 'TB'},node_attr={'rank':'source','shape':'plaintext'},format='png')
        sbs_d=self.subgroups()
        sbs=[H for j in sbs_d.keys() for H in sbs_d[j]]
        letters = "ABCDEFGHIJKLNNOPQRSTUVWXYZ"
        toletter = {}
        toelem = {}
        for letter, elem in zip(letters, sbs):
            toletter[elem] = letter
            toelem[letter] = elem
        letters = letters[:len(sbs)]
        table=' <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0" CELLPADDING="4"> <TR><TD COLSPAN="2"><B>Subgroups</B></TD></TR>'
        for g in sbs:
            table=table+"<tr><td>"+toletter[g]+"</td><td>"+str(set(g.group_elems))+"</td></tr>"
        table=table+"</TABLE> "
        for g in sbs:
            G.node(repr(g),label=toletter[g],shape='circle',color='Cyan',style='filled')
        edges=[(a,b) for a in sbs for b in sbs if (b <= a) and (a!=b)]
        for e in edges:
            G.edge(repr(e[0]),repr(e[1]),color='Red',dir='back')
        png_str = G.render(cleanup=True)
        display(HTML(table),Image(png_str))

    def CayleyGraph(self):
        from IPython.display import Image,SVG,display
        import graphviz as gv
        G=gv.Digraph(format='png',engine='circo')
        elems=[g for g in self.group_gens]
        vertices=[repr(a) for a in self]
        for v in vertices:
            G.node(v)
        letters = "abcdefghijklmnopqrstuvwxyz"
        colors = ['Red','Blue','Green','Yellow','SkyBlue','PaleGreen','Lime','Tan','YellowGreen',
              'Violet','Tomato','Plum','Magenta','Mocassin','LightPink', 'LightCyan','Khaki',
              'Ivory','Gray','Fuchsia','Coral','Bisque','Aqua','Azure','DeepPink','Gainsboro',
              'HotPink']
        toletter = {}
        toelem = {}
        for letter, elem in zip(letters, elems):
            toletter[elem] = letter
            toelem[letter] = elem
        letters = letters[:len(elems)]
        tocelem = {}
        tocolor = {}
        for elem, color in zip(elems,colors):
            tocolor[elem] = color
            tocelem[color] = elem
        colors = colors[:len(elems)]
        E={}
        for i in range(len(elems)):
            E[i]=[(repr(a),repr(b)) for a in self for b in self if b==a*elems[i]]
            for e in E[i]:
                G.edge(e[0],e[1],toletter[elems[i]],_attributes={'color':tocolor[elems[i]]})
        png_str = G.render(cleanup=True)
        display(Image(data=png_str))

    def automorphism_identity(self):
        return GroupHomomorphism(self, self,lambda x: x,check_morphism_axioms=False)

    def AutomorphismGroup(self):
        """Group of automorphisms of self"""
        dicts=[]
        # Try to match the generators of self with some subset of other
        A = self.group_gens
        for B in itertools.permutations(self.group_elems, len(A)):

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
                dicts.append(func)
        def fn(d):
            return lambda x:d[x]
        Gr=Set([GroupHomomorphism(self,self,fn(d)) for d in dicts])
        bin_op= Function(Gr.cartesian(Gr), Gr, lambda x: x[0].homomorphism_compose(x[1]),
                     check_well_defined=False)
        return Group(Gr, bin_op,check_ass=False,check_inv=False,identity=self.automorphism_identity())

    def automorphism_by_conjugation(self,other):
        return GroupHomomorphism(self, self,lambda x: other*x*other**-1,check_morphism_axioms=False)

    def InnerAutomorphismGroup(self):
        Gr=Set([self.automorphism_by_conjugation(g) for g in self])
        bin_op= Function(Gr.cartesian(Gr), Gr, lambda x: x[0].homomorphism_compose(x[1]),check_well_defined=False)
        return Group(Gr, bin_op,check_ass=False,check_inv=False,identity=self.automorphism_identity(), parent=self.AutomorphismGroup())

    def AllHomomorphisms(self,other):
        """List of homomorphisms of self to other"""
        dicts=[]
        # Try to match the generators of self with some subset of other
        A = self.group_gens
        for B in itertools.permutations(other.group_elems, len(A)):
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
                func.update(noobs)
            if not counterexample:
                dicts.append(func)
        def fn(d):
            return lambda x:d[x]
        return [GroupHomomorphism(self,other,fn(d)) for d in dicts]

class GroupHomomorphism(Function): #we should add here check_well_defined, and check_group_axioms as options
    """
    The definition of a Group Homomorphism

    A GroupHomomorphism is a Function between Groups that obeys the group
    homomorphism axioms.

    Args:
        domain, codomain and function. domain and codomain are groups, and function is the map

    Example:
        >>> G=CyclicGroup(2)
        >>> H=G.cartesian(G)
        >>> f=GroupHomomorphism(H,G, lambda x:G(x.elem[1]))
        >>> f.kernel()
        Group with 2 elements
        >>> f.is_surjective()
        True
    """

    def __init__(self, domain, codomain, function, check_morphism_axioms=True):
        """Check types and the homomorphism axioms; records the two groups"""

        if not isinstance(domain, Group):
            raise TypeError("domain must be a Group")
        if not isinstance(codomain, Group):
            raise TypeError("codomain must be a Group")
        if not all(function(elem) in codomain for elem in domain):
            raise TypeError("Function returns some value outside of codomain")

        if check_morphism_axioms:
            if not all(function(a * b) == function(a) * function(b) \
                       for a in domain for b in domain):
                raise ValueError("function doesn't satisfy the homomorphism axioms")

        self.domain = domain
        self.codomain = codomain
        self.function = function

    def __call__(self,other):
        return self.function(other)

    def __hash__(self):
        return hash(self.domain) + 2 * hash(self.codomain)

    def __eq__(self, other):
        if not isinstance(other, GroupHomomorphism):
            return False

        return self.domain == other.domain and self.codomain==other.codomain and all(self.function(a)==other.function(a) for a in self.domain)

    def __ne__(self, other):
        return not self == other

    def __str__(self):
        if not(self.domain==self.codomain):
            return "Group homomorphism between "+str(self.domain)+" and "+str(self.codomain)
        return "Group endomorphism of "+str(self.domain)

    def __repr__(self):
        if not(self.domain==self.codomain):
            return "Group homomorphism"
        return "Group endomorphism"

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

    def homomorphism_compose(self,other):
        if not self.domain == other.codomain:
            raise ValueError("codomain of other must match domain of self")
        return GroupHomomorphism(other.domain, self.codomain,lambda x: self(other(x)), check_morphism_axioms=False)

    def automorphism_inverse(self):
        if not self.function.is_bijective():
            raise ValueError("self must be bijective")
        l={}
        for x in self.domain:
            l[x]=self(x)
        inv = {v: k for k, v in l.items()}
        return GroupHomomorphism(self.codomain, self.domain,lambda x: inv[x], check_morphism_axioms=False)


class GroupAction: #we should add here check_well_defined, and check_group_axioms as options
    """
    The definition of a Group Action

    A Group Action is a Function from the cartasian product of a set X and a group G to X, fulfilling some properties

    Example:
        >>> from Group import *
        >>> G=SymmetricGroup(3)
        >>> f=GroupAction(G,Set({1,2,3}),lambda x,y:x.elem(y))
        >>> p=G(permutation(2,3,1))
        >>> f.function(p,3)
        1
        >>> f.orbit(2)
        frozenset({1, 2, 3})
        >>> f.stabilizer(3)
        Group with 2 elements
        >>> list(_)
        [( ),  (1, 2)]
    """

    def __init__(self, group, theset, function, check_action_axioms=True):
        """Check types and the homomorphism axioms; records the two groups"""

        if not isinstance(group, Group):
            raise TypeError("The first argument must be a Group")
        if not isinstance(theset, Set):
            raise TypeError("The secon argument must be a Set")
        # f(g,x) maps to X with g in the group and x in the set
        if not all(function(g,x) in theset for g in group for x in theset):
            raise TypeError("Function returns some value outside of codomain")

        if check_action_axioms:
            #first axiom a*(b*x)=(a b)*x
            if not all(function(a,function(b,x)) == function(a*b,x) \
                       for a in group for b in group for x in theset):
                raise ValueError("function doesn't satisfy the first action axiom")
            #second axiom
            if not all(function(group.e, x)==x for x in theset):
                raise ValueError("function doesn't satisfy the second action axiom")

        self.group = group
        self.set = theset
        self.function = function

    def __str__(self):
        return "Group action"

    def __repr__(self):
        return "Group action from ("+str(self.group)+")x("+str(self.set)+") to "+str(self.set)

    def __call__(self,g,el):
        return self.function(g,el)


    # def orbit(self,other):
    #     if not(other in self.set):
    #         raise ValueError("other must be in self.set")
    #     degree=len(self.set)
    #     gens=self.group.group_gens
    #     other=[other]
    #     orb = other
    #     used = [False]*(degree+1)
    #     for el in other:
    #         used[el] = True
    #     for b in orb:
    #         for gen in gens:
    #             temp = self.function(gen,b)
    #             if used[temp] == False:
    #                 orb.append(temp)
    #                 used[temp] = True
    #     return Set(orb)

    def orbit(self, other):
        if not(other in self.set):
            raise ValueError("other must be in self.set")
        return Set([self.function(a,other) for a in self.group])

    # def orbits(self):
    #    """Compute the orbits of G.
    #    """
    #    degree=len(self.set)
    #    seen = set()  # elements that have already appeared in orbits
    #    orbs = []
    #    sorted_I = list(range(1,degree+1))
    #    I = set(sorted_I)
    #    while I:
    #        i = sorted_I[0]
    #        orb = self.orbit(i)
    #        orbs.append(orb)
    #        # remove all indices that are in this orbit
    #        I -= orb
    #        sorted_I = [i for i in sorted_I if i not in orb]
    #    return orbs

    def orbits(self):
        lels=list(self.set)
        lorb=[]
        while len(lels)>0:
            el=lels[0]
            orb=self.orbit(el)
            lorb.append(orb)
            lels=[g for g in lels if not(g in orb)]
        return lorb
    
    # def stabilizer(self,other):
    #     if not(other in self.set):
    #         raise ValueError("other must be in self.set")
    #     G=self.group
    #     degree=len(self.set)
    #     orb = [other]
    #     table = {other: G(G.e.elem)}
    #     table_inv = {other: G(G.e.elem)}
    #     used = [False]*(degree+1)
    #     used[other] = True
    #     gens=G.group_gens
    #     stab_gens = []
    #     for b in orb:
    #         for gen in gens:
    #             temp = self.function(gen,b)
    #             if used[temp] is False:
    #                 gen_temp = gen*table[b]
    #                 orb.append(temp)
    #                 table[temp] = gen_temp
    #                 table_inv[temp] = gen_temp**-1
    #                 used[temp] = True
    #             else:
    #                 schreier_gen = table_inv[temp]*gen*table[b]
    #                 if schreier_gen not in stab_gens:
    #                     stab_gens.append(schreier_gen)
    #     return G.generate(stab_gens)

    def stabilizer(self,other):
        if not(other in self.set):
            raise ValueError("other must be in self.set")
        G=Set([a.elem for a in self.group if self.function(a,other)==other])
        return Group(G,self.group.bin_op.new_domains(G.cartesian(G), G, check_well_defined=False),parent=self.group, check_ass=False,check_inv=False,identity=self.group.e.elem)

    def orbit_transversal(self,other, pairs):
        """Computes a transversal for the orbit of ``alpha`` as a set.
        For a permutation group ``G``, a transversal for the orbit
        ``Orb = \{g(\alpha) | g \in G\}`` is a set
        ``\{g_\beta | g_\beta(\alpha) = \beta\}`` for ``\beta \in Orb``.
        Note that there may be more than one possible transversal.
        If ``pairs`` is set to ``True``, it returns the list of pairs
        ``(\beta, g_\beta)``. For a proof of correctness, see [1], p.79
        """
        G=self.group
        degree=len(self.set)
        tr = [(other,G(G.e.elem))]
        used = [False]*(degree+1)
        used[other] = True
        gens=self.group.group_gens
        for x, px in tr:
            for gen in gens:
                temp = self.function(gen,x)
                if used[temp] == False:
                    tr.append((temp, gen*px))
                    used[temp] = True
        if pairs:
            return tr
        return [y for _, y in tr]

    def is_transitive(self):
        got_orb = False
        for x in self.orbits():
            if len(x) > 1:
                if got_orb:
                    return False
                got_orb = True
        return got_orb

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
        Gr= Group(G, bin_op,check_ass=False,check_inv=False,identity=0, abelian=True, group_order=n)
        Gr.group_gens=[Gr(1)]
        return Gr
    if rep=="permutations":
        def rotate_left(x, y):
            if len(x) == 0:
                return []
            y = y % len(x)
            return x[y:] + x[:y]

        def cyclic(n):
            gen = list(range(1,n+1))
            for i in range(n):
                yield permutation(gen)
                gen = rotate_left(gen, 1)
        G=Set(cyclic(n))
        #bin_op = Function(G.cartesian(G), G, lambda x: x[0]*x[1])
        bin_op=SymmetricGroup(n).bin_op.new_domains(G.cartesian(G),G,check_well_defined=False)
        Gr = Group(G, bin_op,check_ass=False,check_inv=False, identity=permutation(list(range(1,n+1))),
        abelian=True, group_order=n, group_degree=n,parent=SymmetricGroup(n))
        Gr.group_gens=[Gr(permutation([tuple(range(1,n+1))]))]
        return Gr
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
        Gr = Group(G, bin_op,check_ass=False,check_inv=False, identity=permutation(list(range(1,n+1))), abelian=False,
        group_order=math.factorial(n), group_degree=n)
        Gr.group_gens=[Gr(permutation([tuple(range(1,n+1))])),Gr(permutation((1,2)).extend(n))]
        return Gr
    if n==2:
        Gr = Group(G, bin_op,check_ass=False,check_inv=False, identity=permutation(list(range(1,3))), abelian=True,
        group_order=2, group_degree=2)
        Gr.group_gens=[Gr(permutation([tuple(range(1,3))]))]
    if n==1:
        Gr = Group(G, bin_op,check_ass=False,check_inv=False, identity=permutation(list(range(1,2))), abelian=True,
        group_order=1, group_degree=1)
        Gr.group_gens=[Gr(permutation([tuple(range(1,2))]))]
    return Gr


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
        Gr=Group(G, bin_op,check_ass=False,check_inv=False,identity=permutation(list(range(1,n+1))),abelian=False,
        group_order=math.factorial(n)//2,parent=SymmetricGroup(n), group_degree=n)
        Gr.group_gens=[Gr.parent(permutation((i,i+1,i+2)).extend(n)) for i in range(1,n-1)]
    if n==2:
        Gr = Group(G, bin_op,check_ass=False,check_inv=False, identity=permutation(list(range(1,3))), abelian=True,
        group_order=1,parent=SymmetricGroup(2), group_degree=2)
        Gr.group_gens=[Gr.parent(permutation(list(range(1,3))))]
    return Gr



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
        Gr=Group(G, Function(G.cartesian(G), G, multiply_symmetries),group_order=2*n)
        Gr.group_gens=[Gr('R1'),Gr('S0')]
        return Gr
    if rep=="permutations":
        def rotate_left(x, y):
            if len(x) == 0:
                return []
            y = y % len(x)
            return x[y:] + x[:y]

        def dihedral(n):
            if n == 1:
                yield permutation([1, 2])
                yield permutation([2, 1])
            elif n == 2:
                yield permutation([1, 2, 3, 4])
                yield permutation([2, 1, 4, 3])
                yield permutation([3, 4, 1, 2])
                yield permutation([4, 3, 2, 1])
            else:
                gen = list(range(1,n+1))
            for i in range(n):
                yield permutation(gen)
                yield permutation(gen[::-1])
                gen = rotate_left(gen, 1)

        G=Set(dihedral(n))
        bin_op = Function(G.cartesian(G), G, lambda x: x[0]*x[1])
        Gr=Group(G, bin_op,check_ass=False,check_inv=False,identity=permutation(list(range(1,2*n+1))),abelian=False,
        group_order=2*n,parent=SymmetricGroup(n), group_degree=n)
        Gr.group_gens=[Gr.parent(permutation([1]+list(range(2,n+1))[::-1])),Gr.parent(permutation([tuple(range(1,n+1))]))]
        return Gr
    raise ValueError("The second argument can be 'RS' or 'permutations'")


def QuaternionGroup(rep="ijk"):
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
    if rep=="ijk":
        q2=[ "1", "-1", "i", "-i", "j", "-j", "k", "-k"]
        table=[[ "1", "-1", "i", "-i", "j", "-j", "k", "-k"],[ "-1", "1", "-i", "i", "-j", "j", "-k", "k"],[ "i", "-i", "-1", "1", "k", "-k", "-j", "j"],[ "-i", "i", "1", "-1", "-k", "k", "j", "-j"],[ "j", "-j", "-k", "k", "-1", "1", "i", "-i"],[ "-j", "j", "k", "-k", "1", "-1", "-i", "i"],[ "k", "-k", "j", "-j", "-i", "i", "-1", "1"],[ "-k", "k", "-j", "j", "i", "-i", "1", "-1"]]
        def product(a,b):
            i=q2.index(a)
            j=q2.index(b)
            return table[i][j]
        G=Set(q2)
        return Group(G,Function(G.cartesian(G),G, lambda x: product(x[0],x[1])))
    if rep=="permutations":
        q1=[permutation([1, 2, 3, 4, 5, 6, 7, 8]), permutation([2, 3, 4, 1, 6, 8, 5, 7]),
            permutation([3, 4, 1, 2, 8, 7, 6, 5]), permutation([4, 1, 2, 3, 7, 5, 8, 6]),
            permutation([5, 7, 8, 6, 3, 2, 4, 1]), permutation([6, 5, 7, 8, 4, 3, 1, 2]),
            permutation([7, 8, 6, 5, 2, 1, 3, 4]), permutation([8, 6, 5, 7, 1, 4, 2, 3])]
        G=Set(q1)
        bin_op = Function(G.cartesian(G), G, lambda x: x[0]*x[1])
        return Group(G, bin_op)
    raise ValueError("The second argument must be 'ijk' or 'permutations'")

# def QuaternionGroup(rep="ijk"):
#     """
#     The quaternion group Q2; its elments are 1,i,j,k and their oposite
#
#     Example:
#         >>> Q2=QuaternionGroup()
#         >>> list(Q2)
#         ['1', 'i', 'k', 'j', '-i', '-k', '-j', '-1']
#         >>> i=Q2("i")
#         >>> j=Q2("j")
#         >>> i*j
#         'k'
#         >>> j*i
#         '-k'
#     """
#
#     if rep=="ijk":
#         q2=[ "1", "-1", "i", "-i", "j", "-j", "k", "-k"]
#         table=[[ "1", "-1", "i", "-i", "j", "-j", "k", "-k"],[ "-1", "1", "-i", "i", "-j", "j", "-k", "k"],[ "i", "-i", "-1", "1", "k", "-k", "-j", "j"],[ "-i", "i", "1", "-1", "-k", "k", "j", "-j"],[ "j", "-j", "-k", "k", "-1", "1", "i", "-i"],[ "-j", "j", "k", "-k", "1", "-1", "-i", "i"],[ "k", "-k", "j", "-j", "-i", "i", "-1", "1"],[ "-k", "k", "-j", "j", "i", "-i", "1", "-1"]]
#         def product(a,b):
#             i=q2.index(a)
#             j=q2.index(b)
#             return table[i][j]
#         G=Set(q2)
#         bin_op = Function(G.cartesian(G), G, lambda x: product(x[0],x[1]))
#         Gr=Group(G,Function(G.cartesian(G),G, bin_op),check_ass=False,check_inv=False,identity="1",abelian=False,
#         group_order=8)
#         Gr.group_gens=[Gr('i'),Gr('j')]
#         return Gr
#     if rep=="permutations":
#         q1=[permutation([1, 2, 3, 4, 5, 6, 7, 8]), permutation([2, 3, 4, 1, 6, 8, 5, 7]),
#             permutation([3, 4, 1, 2, 8, 7, 6, 5]), permutation([4, 1, 2, 3, 7, 5, 8, 6]),
#             permutation([5, 7, 8, 6, 3, 2, 4, 1]), permutation([6, 5, 7, 8, 4, 3, 1, 2]),
#             permutation([7, 8, 6, 5, 2, 1, 3, 4]), permutation([8, 6, 5, 7, 1, 4, 2, 3])]
#         G=Set(q1)
#         bin_op = Function(G.cartesian(G), G, lambda x: x[0]*x[1])
#         Gr=Group(G, bin_op,check_ass=False,check_inv=False,identity=permutation([1, 2, 3, 4, 5, 6, 7, 8]),
#         abelian=False, group_order=8, group_degree=8, parent=SymmetricGroup(8))
#         Gr.group_gens=[Gr.parent(permutation([2, 3, 4, 1, 6, 8, 5, 7])),Gr.parent(permutation([4, 1, 2, 3, 7, 5, 8, 6]))]
#         return Gr
#     raise ValueError("The second argument must be 'ijk' or 'permutations'")

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

        G=Set([permutation([1,2,3,4]),permutation((1,2),(3,4)),permutation((1,3),(2,4)),permutation((1,4),(2,3))])
        #bin_op = Function(G.cartesian(G), G, lambda x: x[0]*x[1])
        bin_op=AlternatingGroup(4).bin_op.new_domains(G.cartesian(G),G,check_well_defined=False)
        Gr=Group(G, bin_op,check_ass=False,check_inv=False,identity=permutation([1, 2, 3, 4]),
        abelian=True,parent=AlternatingGroup(4), group_order=4, group_degree=4)
        Gr.group_gens=[Gr.parent(permutation((1,2),(3,4))), Gr.parent(permutation((1,3),(2,4)))]
        return Gr
    raise ValueError("The second argument can be 'RS' or 'permutations'")

def DiCyclicGroup():
    a=permutation([(1,2),(3,4),(5,6,7)])
    b=permutation([(1,3,2,4),(5,7)])
    G=Set([a**i for i in range(6)]+[a**i*b for i in range(6)])
    bin_op = Function(G.cartesian(G), G, lambda x: x[0]*x[1])
    Gr=Group(G, bin_op,check_ass=False,check_inv=False,identity=permutation([1,2,3,4,5,6,7]),abelian=False,
    group_order=8,group_degree=7)
    Gr.group_gens=[Gr(a),Gr(b)]
    return Gr

def GroupOfUnitsModInt(n):
    G=Set([m for m in range(n) if gcd(n,m)==1])
    bop=Function(G.cartesian(G),G,lambda x: (x[0]*x[1])%n,check_well_defined=False)
    return Group(G,bop, check_inv=False, check_ass=False, abelian=True, identity=1,group_order=totient(n))

def ElementaryDivisors(n):
    def partition(n):
        a = [0 for i in range(n + 1)]
        k = 1
        y = n - 1
        while k != 0:
            x = a[k - 1] + 1
            k -= 1
            while 2 * x <= y:
                a[k] = x
                y -= x
                k += 1
            l = k + 1
            while x <= y:
                a[k] = x
                a[l] = y
                yield a[:k + 2]
                x += 1
                y -= 1
            a[k] = x + y
            y = x + y - 1
            yield a[:k + 1]
    factored=factorint(n)
    factored2={}
    for i in factored.keys():
        factored2[i]=list(partition(factored[i]))
    E=[[[(lambda x: k**x)(i) for i in factored2[k][j]] for j in range(len(factored2[k]))] for k in factored2]
    Econ=[[]]
    for i in range(len(E)):
        Econ=[a+[b] for a in Econ for b in E[i]]
    return Econ

def AbelianGroups(n,option="ElementaryDivisors"):
    if option=="ElementaryDivisors":
        E=ElementaryDivisors(n)
    elif option=="InvariantFactors":
        E=InvariantFactors(n)
    else:
        raise ValueError("The option is ElementaryDivisors (defect) or InvariantFactors")
    Res=[[CyclicGroup(m) for m in flatten(h)] for h in E]
    l=Res[0]
    def car(l):
        G=l[0]
        if len(l)==1:
            return G
        return G.cartesian(car(l[1:]))
    total=[car(l) for l in Res]
    return total

def InvariantFactors(n):
    E=ElementaryDivisors(n)
    H=[]
    for B in E:
        L=[]
        A=deepcopy(B)
        while len(A)!=0:
            a=functools.reduce(operator.mul,[h.pop() for h in A])
            L.append(a)
            while [] in A:
                A.remove([])
        H.append(L)
    return H

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

    def __call__(self,n):
        return self.tuple[n-1]

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
    def extend(self,n):
        """
        Extends the permutation to a permutation of the set {1..n} leaving the elements above its length untouched
        """
        if not(isinstance(n,int)) or (n<self.length):
            raise ValueError("Either the argument is not an integer or it is less than the length of the permuataion")
        tmp=list(range(1,n+1))
        for i in range(self.length):
            tmp[i]=(self.tuple)[i]
        return permutation(tmp)
