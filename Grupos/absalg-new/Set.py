"""
Implementation of Set
"""
import itertools
class Set(frozenset):
    """
    Definition of a Set

    It's important that Set be a subclass of frozenset, (not set), because:
    1) it makes Set immutable
    2) it allows Set to contains Sets
    """
    def __repr__(self):
        return str(set(self))

    def __str__(self):
        return str(set(self))

    #def __mul__(self, other):
    def cartesian(self, other):
        """Cartesian product"""
        if not isinstance(other, Set):
            raise TypeError("One of the objects is not a set")
        return Set(itertools.product(self,other, repeat=1))
        #return Set((a,b) for a in self for b in other)


    def pick(self):
        """Return an arbitrary element. (The finite Axiom of Choice is true!)"""

        if len(self) == 0:
            raise KeyError("This is an empty set")

        for item in self: break
        return item
