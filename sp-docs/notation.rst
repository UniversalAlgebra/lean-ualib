.. math:: 

    \newcommand\FGrp{F_{\mathbf{Grp}}} \newcommand\inj{\mathrm{in}} \newcommand\inji{\mathrm{in}_i} \newcommand\hom{\operatorname{Hom}} \newcommand\epi{\operatorname{Epi}} \newcommand\aut{\operatorname{Aut}} \newcommand\mono{\operatorname{Mono}}`


Notation
========

The symbols :math:`\mathbb{N}`, :math:`\omega`, and ``nat`` are used interchangeably; they all denote the set of natural numbers.

If :math:`m` is a natural number, we write :math:`m \colon \mathbb N` and say ":math:`m` has type :math:`\mathbb N`."

(For the reader unfamiliar with type theory, it's safe in the beginning to think of this as meaning :math:`n\in \mathbb N`.)

For :math:`m \colon \mathbb N`, we denote and define :math:`\underline{m} = \{0, 1, \dots, m-1\}`.

Let :math:`a = (a_0, a_1, \dots, a_{m-1})` be an `mtuple <composition>`__ of elements from :math:`A`.

As we will explain in the section on `Composition of operations <composition>`__, the tuple :math:`a` may be identified with a function of type :math:`\underline{m} \to A`, where :math:`a(i) = a_i`, for each :math:`i<m`.)

If :math:`h \colon A \to A`, then :math:`h\circ a : \underline{m} \to A` is the function whose :math:`i`-th coordinate is :math:`(h\circ a)(i) = h(a(i)) = h(a_i)`, and we may formally identify the function :math:`h \circ a : \underline{m} \to A` with its "image tuple" :math:`(h(a_0), h(a_1), \dots, h(a_{m-1}))`.

.. index:: signature, arity

**The Classical Notion of Signature**.

A **signature** :math:`S = (F, \rho)` consists of a set :math:`F` of operation symbols and a function :math:`\rho \colon F \to \mathbb{N}`. We call :math:`\rho f` the **arity** of the symbol :math:`f`.

If :math:`A` is a set and :math:`f` is a :math:`\rho f`-ary operation on :math:`A`, then we may write :math:`f \colon A^{\rho f} \to A`.

On the other hand, as the natural number :math:`\rho f` denotes the set :math:`\{0, 1, \dots, \rho f -1\}`, a function :math:`a \colon \rho f \to A` can be identified with its graph, which is simply a :math:`\rho f`-tuple of elements from :math:`A`; that is, :math:`a i : A`, for each :math:`i: \rho f`.

Then, by identifying the :math:`\rho f`-th power :math:`A^{\rho f}` with the type :math:`\rho f \to A` of functions from :math:`\{0, 1, \dots, \rho f -1\}` to :math:`A`, we thus identify the function type :math:`A^{\rho f} \to A` with the type :math:`(\rho f \to A) \to A`.

**Examples.**

  (a) Suppose

      - :math:`g \colon (\underline{m} \to A) \to A` is an :math:`\underline{m}`-ary operation on :math:`A`, and
      - :math:`a : \underline{m} \to A`.

      Then :math:`g a = g(a_0, a_1, \dots, a_{m-1})` has type :math:`A`.

  (b) Suppose

      - :math:`f \colon (\rho f \to B) \to B` is a :math:`\rho f`-ary operation on :math:`B`
      - :math:`a \colon \rho f \to A` is a :math:`\rho f`-tuple on :math:`A`, and
      - :math:`h \colon A \to B`.

      Then :math:`h \circ a` has type :math:`\rho f \to B` and :math:`f (h \circ a)` has type :math:`B`.

It is important to be familiar with the classical notions of signature and arity, since these are used by almost all algebraists. However, in the section on :ref:`F-algebras <f-algebras>`, we give alternative definitions of these basic notions that will turn out to be easier to compute with.

Notation for Homs, Epis, Monos, Autos
-------------------------------------

If :math:`\mathbf A = (A, f^A)` and :math:`\mathbf B = (B, f^B)` are algebras, we denote and define

+ :math:`\hom(\mathbf A, \mathbf B) =` homomorphisms from :math:`\mathbf A` to :math:`\mathbf B`.
+ :math:`\epi(\mathbf A, \mathbf B) =` epimorphisms from :math:`\mathbf A` onto :math:`\mathbf B`.
+ :math:`\mono(\mathbf A, \mathbf B) =` monomorphisms from :math:`\mathbf A` into :math:`\mathbf B`.
+ :math:`\aut(\mathbf A, \mathbf B) =` automorphisms from :math:`\mathbf A` into and onto :math:`\mathbf B`.

------------------------------

.. blank
