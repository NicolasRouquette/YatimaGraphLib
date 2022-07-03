# Extracting Yatima's Lean4 Graph library as a standalone generic library

The [Yatima language](https://github.com/yatima-inc/yatima-lang) compiler 
features an interesting monadic formulation of the strongly connected components algorithm for directed graphs, see [Yatima/Compiler/Graph.lean#L37:L226](https://github.com/yatima-inc/yatima-lang/blob/ada78d298e08e495b307cb639f4305731f3af663/Yatima/Compiler/Graph.lean#L37:L226).

Unfortunately, this Graph data structure is currently tied to the Lean4 representation of Lean4 symbols, see [Yatima/Compiler/Graph.lean#L32:L34](https://github.com/yatima-inc/yatima-lang/blob/ada78d298e08e495b307cb639f4305731f3af663/Yatima/Compiler/Graph.lean#L32-L34).

As a Lean4 programming exercise, I wanted to see if I could extract this Graph library and parameterize it for an arbitrary type of vertex. This repo is the result of this exercise.
