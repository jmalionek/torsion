"""
Given a TwistableDomain object corresponding to a 3-manifold, calculates the Thurston norm ball.
"""

import twistable_revamp as tw


def H2_basis_in_C2(DD):
	"""Returns a basis for the second homology as a chain in
	C_2 (the non-dualized version)
	"""
	# Since the manifold is stored as a dirichlet domain with gluing info, B3 should be 0
	# Therefore, ker(B2) is isomorphic to H2
	B2 = DD.B2().change_ring(ZZ)
	ker = B2.right_kernel()
	return ker.basis()


def construct_dual_homology_matrix(DD):
	# First, calculates for each basis vector of H2.
	basis = DD.H2_basis_in_C2()
	cobasis = [None] * len(basis)
	phi = DD.map_to_dual_free_abelianization()
	# If the basis vector contains 1 or -1, then the dual element can be obtained by taking the 1-chain dual to that
	# specific face
	for i, vec in enumerate(basis):
		for j, entry, in enumerate(list(vec)):
			if entry.abs() == 1:
				if entry == 1:
					cobasis[j] = phi(DD.holonomy_generators[i])
				elif entry == -1:
					cobasis[j] = phi(DD.holonomy_inverse_generators[i])
	# If 1 or -1 is not an entry, then the entries must all be coprime. You can find two coprime elements and then
	# use Bezout's identity so that the intersection number will be 1.
	# I think it is highly unlikely that there will NOT be two coprime elements which is why this part is so janky.
	if None in cobasis:
		for i, vec in enumerate(basis):
			if vec is None:
				coeffs = poly.bezout_coeffs(vec)
				tietze = []
				for j, coeff in enumerate(coeffs):
					tietze.extend([coeff.sign() * j] * coeff.abs())
				hol = HolonomyElement(tietze)
				cobasis[i] = phi(hol)
	mat = matrix(ZZ, [g.coefficients() for g in cobasis]).transpose()
	for i, vec in enumerate(basis):
		assert get_dual_coH1_elt(vec, DD, mat) == cobasis[i]
	return mat


def get_dual_coH1_elt(vector, DD, mat=None):
	"""Given a chain representing an element of H_2, by poincare duality there is an element of H^1 which is dual to
	it. By the universal coefficient theorem, H^1 is isomorphic to the free abelianization of H_1.
	This function finds the element in the free abelianization which corresponds to it."""
	if mat is None:
		mat = construct_dual_homology_matrix(DD)
	ker = DD.B2().right_kernel()
	assert vector in ker
	coords = ker.coordinate_vector(vector)
	return DD.free_abelianization(mat * coords)


