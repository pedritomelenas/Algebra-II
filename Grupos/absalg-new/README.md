# Álgebra II
## Extensión de absalg

Esta carpeta contiene una extensión de las funcionalidades de la librería [absalg](https://github.com/naftaliharris/Abstract-Algebra) de [Naftali Harris](http://www.naftaliharris.com).

- Se ha cambiado el producto cartesiano que se denotaba por `G * G` por `G.cartesian(G)`.

- Se ha introducido un nuevo atributo a los grupos: `parent`. Un grupo al crearse, tendrá `parent=None`. Si creamos un subgrupo de `G` a partir de un conjunto de generadores, o bien, el conjunto de subgrupos de `G`, todos tendrán `parent=G`.

- La introducción de `parent` permite hacer intersecciones de subgrupos: `H.intersection(J)`.
