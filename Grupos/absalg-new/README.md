# Álgebra II
## Extensión de absalg

Esta carpeta contiene una extensión de las funcionalidades de la librería [absalg](https://github.com/naftaliharris/Abstract-Algebra) de [Naftali Harris](http://www.naftaliharris.com).

- Se ha cambiado el producto cartesiano que se denotaba por `G * G` por `G.cartesian(G)`.

- Se ha introducido un nuevo atributo a los grupos: `parent`. Un grupo al crearse, tendrá `parent=el mismo`. Si creamos un subgrupo de `G` a partir de un conjunto de generadores, o bien, el conjunto de subgrupos de `G`, todos tendrán `parent=G`.

- La introducción de `parent` permite hacer intersecciones de subgrupos: `H.intersection(J)`.

- Ahora hay también producto de subgrupos.

- Se han incluido check_ass, check_inv, identity y abelian como posibles argumentos de `Group` para evitar detectar si el magma es asociativo, cerrado para inversos, tiene elemento neutro y si es o no abeliano. Entre otras ventajas, esto hace que $S_4\times S_4$ no tarde una eternidad en calcularse.

- Todo esto se usa en el producto cartesiano, producto, intersección, subrupos y subgrupos generados por elementos.

- Hay una nueva función que calcula tuplas a partir de un ciclo, que luego se puede usar para definir elementos en `Sn(k)`.

```python
In [10]: t=cycle((1,2),3)
In [12]: S3=Sn(3)
GroupElem(t,S3).elem​
Out[12]: (2, 1, 3)
```
