<script type="text/javascript" src="http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML"></script>


# Repaso

##Operaciones con conjuntos


Para declarar conjuntos podemos asignar a una variable una secuencia de
valores entre llaves. Como conjunto, un objeto tiene asociada varias
funciones, como pueden ser la intersección, unión, diferencia de
conjuntos...

    sage: A=Set({1,2,3})
    sage: B=Set([3,5,6,7])

Así por ejemplo, para calcular $A\cup B$ tecleamos:

    sage: A.union(B)
    {1, 2, 3, 5, 6, 7}

Y análogamente para $A\cap B$

    sage: A.intersection(B)
    {3}

Para la diferencia de conjuntos, $A\setminus B$ usamos difference

    sage: A.difference(B)
    {1, 2}

Para pertenencia, por ejemplo, $3\in A$, podemos utilizar:

    sage: 3 in A
    True

El cardinal de un conjunto

    sage: A.cardinality();
    3

Inclusión de conjuntos en ambos sentidos

    sage: A.issuperset(B)
    False

    sage: U=A.union(B)
    sage: A.issubset(U)
    True

Podemos comprobar si es finito

    sage: A.is_finite()
    True

O vacío

    sage: A.is_empty()
    False

O calcular operaciones con conjuntos ya predefinidos. Por ejemplo,
podemos calcular los elementos de $A$ que no son primos

    sage: A.difference(Primes())
    {1}

El conjunto potencia, o de subconjuntos de un conjunto se calcula de la
siguiente forma

    sage: A.subsets()
    Subsets of {1, 2, 3}

Si lo que queremos es que nos muestre los elementos, podemos usar .list;
en este caso \_ sirve para utilizar la última salida

    sage: _.list()
    [{}, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}]

Podemos ver también todos los subconjuntos de dos elementos

    sage: A.subsets(2).list()
    [{1, 2}, {1, 3}, {2, 3}]

Podemos hacer productos cartesianos de listas o conjuntos

    sage: C=CartesianProduct(A,B)

    sage: C.cardinality()
    12

    sage: C.list()
    [[1, 3],
     [1, 5],
     [1, 6],
     [1, 7],
     [2, 3],
     [2, 5],
     [2, 6],
     [2, 7],
     [3, 3],
     [3, 5],
     [3, 6],
     [3, 7]]

# Lógica proposicional

Los operadores lógicos más comunes se pueden escribir de la siguiente
forma:

- '&' para el y

- '|' para el o

- '\^' (acento circunflejo) para el o exclusivo

- '-\>' para la implicación

- '\~' para la negación

- '\<-\>' para el si y sólo si

Con esta convención podemos capturar una fórmula a partir de una cadena
de caracteres

    sage: f= propcalc.formula("(a->b)->a")

Y podemos interpretarla dando valores a las proposiciones atómicas que
en ella aparecen

    sage: f.evaluate({'a':True, 'b':False})
    True

O bien podemos mostrar su tabla de verdad

    sage: f.truthtable()
    a      b      value
    False  False  False  
    False  True   False  
    True   False  True   
    True   True   True   

Veamos ahora con un axioma de la lógica proposicional

    sage: a1=propcalc.formula("a->(b->a)")

Su tabla de verdad siempre da verdadero

    sage: a1.truthtable()
    a      b      value
    False  False  True   
    False  True   True   
    True   False  True   
    True   True   True   

Podemos preguntar si una fórmula es una tautología, una contradicción o
si es satisfacible

    sage: f.is_tautology()
    False

    sage: (f&~f).is_contradiction()
    True

    sage: a1.is_tautology()
    True

    sage: f.is_satisfiable()
    True

    sage: ff=f|~f

    sage: ff.is_tautology()
    True

Podemos también determinar si un conjunto de fórmulas es o no
consistente, y si una fórmula es consecuencia lógica de otras

    sage: f, g, h, i = propcalc.get_formulas("a->(b->c)", "a", "~c", "~b")

    sage: propcalc.consistent(f,g,h,i)
    True

    sage: f, g, h, i = propcalc.get_formulas("a->(b->c)", "a", "~c", "b")

    sage: propcalc.consistent(f,g,h,i)
    False

Sabemos por ejemplo que $\{a\to(b\to c), a,\neg c\}\models \neg b$

    sage: propcalc.valid_consequence(~i,f,g,h)
    True
