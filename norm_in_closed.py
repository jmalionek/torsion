"""
Code here is a reworking of some that came with

https://arxiv.org/abs/1108.3045

which had completely succumbed to bitrot due to changes in Regina,
Sage, and SnapPy.  Specifically, only

1. euler_of_dual_surface

2. dual_surface_quads

3. is_obviously_a_surface_group

are essentially copied, all the other stuff was written from scratch
or borrowed from other projects.

It has not been validated against the data that comes with that paper.
"""


import snappy
from snappy.snap.t3mlite import Mcomplex, OneSubsimplices, V0, V1, V2, V3
import tempfile, string, os, glob
from sage.all import ChainComplex, PermutationGroup
import regina


def closed_snappy_to_t3m(manifold):
    """
    >>> M = snappy.Manifold('m125')  # Exterior of (-2, 3, 8)
    >>> M.dehn_fill([(11,  27), (5, -3)])
    >>> M.homology()
    Z
    >>> T = closed_snappy_to_t3m(M)
    >>> T.LinkGenera
    [0]
    """
    if isinstance(manifold, str):
        manifold = snappy.Triangulation(manifold)
    if True in manifold.cusp_info('is_complete'):
        raise ValueError('Expected a closed manifold')
    T = manifold.filled_triangulation()
    T.simplify()
    S = Mcomplex(T)
    S.smash_all_edges()
    assert S.LinkGenera == [0]
    return S


def cochain_complex(mcomplex):
    mats = mcomplex.boundary_maps()  # for homology
    differential = {i:mats[i].pari.sage().transpose() for i in range(3)}
    return ChainComplex(differential)


def first_cohomology_basis(mcomplex):
    """
    >>> T = closed_snappy_to_t3m('L5a1(0, 1)(0, 1)')
    >>> len(first_cohomology_basis(T))
    2
    """
    C = cochain_complex(mcomplex)
    assert set(C.homology(1).invariants()) == {0}
    return [cocycle.vector(1) for factor, cocycle in C.homology(1, generators=True)]


def get_signed_weight(cohom, tet, a, b):
    sign = tet.Class[a | b].orientation_with_respect_to(tet, a, b)
    return sign * cohom[tet.Class[a | b].index()]


def euler_of_dual_surface(mcomplex, cocycle=None):
    """
    Compute the euler characteristic of the normal surface associated
    to the piecewise affine map to the circle given by the particular
    cohomology class.

    >>> T = closed_snappy_to_t3m('K8n1(0, 1)')
    >>> euler_of_dual_surface(T)
    -2
    """
    if cocycle == None:
        gens = first_cohomology_basis(mcomplex)
        assert len(gens) == 1
        cocycle = gens[0]

    V = 0
    for w in cocycle:
        V = V + abs(w)

    E , F = 0, 0
    for tet in mcomplex.Tetrahedra:
        E_change = 0
        for edge in OneSubsimplices:
            ind = tet.Class[edge].index()
            E_change = E_change + abs(cocycle[ind])

        E = E + 0.5 * E_change

        a = get_signed_weight(cocycle, tet, V0, V1)
        b = get_signed_weight(cocycle, tet, V0, V2)
        c = get_signed_weight(cocycle, tet, V0, V3)

        trans = [0, a, b, c]
        F = F + (max(trans) - min(trans))

    ans = int(F - E + V)
    assert ans == F - E + V
    return ans


def closed_isosigs(snappy_manifold, trys=20, max_tets=50):
    """
    Generate a slew of 1-vertex triangulations of a closed manifold
    using SnapPy.

    >>> M = snappy.Manifold('m004(1,2)')
    >>> len(closed_isosigs(M, trys=5)) > 0
    True

    This code was originally used as part of:

    https://arxiv.org/abs/1812.11940
    """
    M = snappy.Manifold(snappy_manifold)
    assert M.cusp_info('complete?') == [False]
    surgery_descriptions = [M.copy()]

    try:
        for curve in M.dual_curves():
            N = M.drill(curve)
            N.dehn_fill((1,0), 1)
            surgery_descriptions.append(N.filled_triangulation([0]))
    except snappy.SnapPeaFatalError:
        pass

    if len(surgery_descriptions) == 1:
        # Try again, but unfill the cusp first to try to find more
        # dual curves.
        try:
            filling = M.cusp_info(0).filling
            N = M.copy()
            N.dehn_fill((0, 0), 0)
            N.randomize()
            for curve in N.dual_curves():
                D = N.drill(curve)
                D.dehn_fill([filling, (1,0)])
                surgery_descriptions.append(D.filled_triangulation([0]))
        except snappy.SnapPeaFatalError:
            pass

    ans = set()
    for N in surgery_descriptions:
        for i in range(trys):
            T = N.filled_triangulation()
            if T._num_fake_cusps() == 1:
                n = T.num_tetrahedra()
                if n <= max_tets:
                    ans.add((n, T.triangulation_isosig(decorated=False)))
            N.randomize()

    return [iso for n, iso in sorted(ans)]


def genus_from_euler(chi):
    assert chi % 2 == 0
    return 1 - chi//2


def search_for_small_norm_surface(snappy_manifold, lower_bound=None):
    """
    TODO: WHAT ARE THE ASSUMPTIONS HERE?

    I think just that the manifold has b_1 = 1 and no nonseparating
    2-spheres.

    >>> Conway = snappy.Manifold('11n34(0, 1)')
    >>> KT = snappy.Manifold('11n42(0, 1)')
    >>> search_for_small_norm_surface(Conway, 3)
    3
    >>> search_for_small_norm_surface(KT, 2)
    2
    """
    M = snappy_manifold
    assert M.homology().betti_number() == 1
    if lower_bound is None:
        lower_bound = M.alexander_polynomial().degree()//2

    T = closed_snappy_to_t3m(M)
    min_genus = genus_from_euler(euler_of_dual_surface(T))
    if min_genus == lower_bound:
        return min_genus

    for isosig in closed_isosigs(M, trys=20, max_tets=1.5*len(T)):
        T = Mcomplex(isosig)
        new_genus = genus_from_euler(euler_of_dual_surface(T))
        min_genus = min(min_genus, new_genus)
        if min_genus == lower_bound:
            return min_genus

    return min_genus


def dual_surface_quads(mcomplex, cocycle=None):
    """
    Given a triangulation and a cohomology class, return the quad
    types of the dual normal surface.

    The algorithm is simple: Consider the associated affine map of the
    simplex and look at the image heights of the four vertices. The
    quad, if any, must lie between the two vertices with the highest
    images and the two with the lowest image.

    >>> T = closed_snappy_to_t3m('L5a1(0, 1)(0, 1)')
    >>> cocycle = (1, 0, 1, 1, 0, -1, 0)
    >>> dual_surface_quads(T, cocycle)
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]

    Output is in Regina's quad conventions: Q01, Q02, Q03, where Q0i
    is the quad dijoint from the edge joining vertex 0 from vertex i;
    this is the reverse of t3m's.
    """
    if cocycle == None:
        gens = first_cohomology_basis(mcomplex)
        assert len(gens) == 1
        cocycle = gens[0]

    M, C = mcomplex, cocycle
    quadvector = (3*len(M))*[0,]
    for i, tet in enumerate(M.Tetrahedra):
        a = get_signed_weight(C, tet, V0, V1)
        b = get_signed_weight(C, tet, V0, V2)
        c = get_signed_weight(C, tet, V0, V3)

        heights = sorted( [(0,0), (a,1), (b,2), (c,3)] )
        quad_weight = heights[2][0] - heights[1][0]
        if quad_weight:
            rel_positions = [h[1] for h in heights]
            if rel_positions.index(3) < 2:
                t3m_quad = min(rel_positions[:2])
            else:
                t3m_quad = min(rel_positions[2:])

            quad = 2 - t3m_quad
            quadvector[3*i + quad] = quad_weight

    return quadvector


def dual_surface_in_regina(mcomplex, cocycle=None):
    """
    >>> T = closed_snappy_to_t3m('L5a1(0, 1)(0, 1)')  # This is a Euclidean manifold
    >>> basis = first_cohomology_basis(T)
    >>> surfaces = [dual_surface_in_regina(T, c) for c in basis]
    >>> [S.eulerChar() for S in surfaces]
    [0, 0]
    """
    R = mcomplex.regina_triangulation()
    quads = dual_surface_quads(mcomplex, cocycle)
    S = regina.NormalSurface(R, regina.NS_QUAD_CLOSED, quads)
    assert S.eulerChar() == euler_of_dual_surface(mcomplex, cocycle)
    return S


def regina_rel_to_ints(rel):
    """
    >>> G = regina.GroupPresentation(2, ['abAB'])
    >>> regina_rel_to_ints(G.relation(0))
    [1, 2, -1, -2]
    """
    ans = []
    for term in rel.terms():
        e = term.exponent
        g = term.generator
        if e != 0:
            i = (g + 1) if e > 0 else -(g + 1)
            ans = ans + abs(e)*[i]
    assert len(ans) == rel.wordLength()
    return ans


def is_obvious_surface_group(regina_group_presentation):
    """
    Tests whether the given presentation is transparently one of the
    fundamental group of a closed orientable surface.

    >>> G = regina.GroupPresentation(6, ['abABcdCDefEF'])
    >>> is_obvious_surface_group(G)
    True

    The hex torus, so two vertices:
    >>> H = regina.GroupPresentation(6, ['abcABC'])
    >>> is_obvious_surface_group(H)
    False

    Klein bottle:
    >>> N = regina.GroupPresentation(2, ['abaB'])
    >>> is_obvious_surface_group(N)
    False
    """
    G = regina_group_presentation

    # First, we check there is only one relation
    # and that every generator g appears exactly
    # once as g and once as g^-1.

    n = G.countGenerators()
    if G.countRelations() != 1:
        return False
    R = regina_rel_to_ints(G.relation(0))
    if sorted(R) != list(range(-n, 0)) + list(range(1, n+1)):
        return False

    # Now we make sure that we take the boundary
    # of the relator and identify sides accordingly
    # the result is actually a surface.

    perms = []
    for g in range(1, n+1):
        a0, b0 = R.index(g)+1, R.index(-g)+1
        a1 = a0 + 1 if a0 < 2*n else 1
        b1 = b0 + 1 if b0 < 2*n else 1
        perms += [ [(a0, b1)], [(a1, b0)] ]

    return len(PermutationGroup(perms).orbits()) == 1


def is_fiber(regina_surface):
    """
    Returns True if the complement of the surface has *been shown* to be
    F x I, and otherwise False

    >>> T = closed_snappy_to_t3m('K8n1(0, 1)')
    >>> S = dual_surface_in_regina(T)
    >>> is_fiber(S)
    True

    >>> T = closed_snappy_to_t3m('5_2(0, 1)')
    >>> S = dual_surface_in_regina(T)
    >>> is_fiber(S)
    False

    >>> M = snappy.Manifold('m125(11, 27)(5, -3)')
    >>> T = closed_snappy_to_t3m(M)
    >>> S = dual_surface_in_regina(T)
    >>> S.eulerChar()
    -20
    >>> is_fiber(S)
    True
    """
    S = regina_surface
    R = S.triangulation()
    assert R.isClosed() and not R.isIdeal() and S.isConnected()
    F = S.cutAlong()
    F.intelligentSimplify()
    G = F.fundamentalGroup()
    G.intelligentSimplify()
    return is_obvious_surface_group(G)


if __name__ == '__main__':
    import doctest
    doctest.testmod()
