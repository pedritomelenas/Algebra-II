# Álgebra II
## Extensión de absalg

Esta carpeta contiene una extensión de las funcionalidades de la librería [absalg](https://github.com/naftaliharris/Abstract-Algebra) de [Naftali Harris](http://www.naftaliharris.com).

### Permutaciones (nueva clase)

- Tenemos ahora permutaciones: se pueden definir a partir
  -  de listas o secuencias de enteros (representación matricial)
  -  listas o secuencias de tuplas (producto de ciclos; cada tupla es un ciclo)

- Tienen __str__  , __repr__ y __hash__.

- Igualdad (cambiar)

- Composición: p*q corresponde con (p*q)(i)=p(q(i))

- Inverso

- __pow__

- Descomposición en ciclos disjuntos

- Inversiones

- Signo

- Orden

### GroupEleme

- Centralizador de un elemento

- clase de conjugación de un elemento

- Los elementos del grupo tienen `repr`


### Group

- Se han incluido check_ass, check_inv, identity y abelian como posibles argumentos de `Group` para evitar detectar si el magma es asociativo, cerrado para inversos, tiene elemento neutro y si es o no abeliano. Entre otras ventajas, esto hace que $S_4\times S_4$ no tarde una eternidad en calcularse (esto se usa en el producto cartesiano, producto, intersección, subrupos y subgrupos generados por elementos).

- Se ha cambiado el producto cartesiano que se denotaba por `G * G` por `G.cartesian(G)`.

- Se ha introducido un nuevo atributo a los grupos: `parent`. Un grupo al crearse, tendrá `parent=el mismo`. Si creamos un subgrupo de `G` a partir de un conjunto de generadores, o bien, el conjunto de subgrupos de `G`, todos tendrán `parent=G`.

- La introducción de `parent` permite hacer intersecciones de subgrupos: `H.intersection(J)`.

- Ahora hay también producto de subgrupos: `H*G`.

- Clases laterales de subgrupos a*H y H*a

- Añadido AlternatingGroup(n), el grupo alternado

- Cayley table now in colors if in python notebook

- El conjunto de las clases de conjugación de los elementos de un grupo

- Clase de conjugación de un subgrupo

- Centro de un subgrupo

- Normalizador

- Introducido SymmetricGroup, que substituye a Sn. Ahora el grupo simétrico es un grupo de permutationes (nueva clase)

- Introducido DihedralGroup, que substituye a Dn; permite "permutations" o "RS" como representaciones

- Introducido CyclicGroup, que substituge a Zn; permite "integers" o "permutations" como representaciones

- Ahora un grupo es "callable"
```python
>>> G=SymmetricGroup(3)
>>> p=GroupElem(permutation(3,2,1),G)
>>> q=G(permutation(3,2,1))
>>> p==q
True
```

- Los grupos tienen __str__ y __repr__.


## ToDo

- Etiquetas a elementos y grupos

- Conjugate

- Mayor control de tipos de datos

- Evitar ciertas comprobaciones en Function, cuando sabemos que está bien definida; lo mismo para GroupHomomorphism

- Get rid of Set?
