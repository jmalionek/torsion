import time

import representation_theory
import twistable_revamp as tw
import random_knots.knotgenus3.optimize as optimize
import permutation_groups
import representation_theory as rep_theory
import polynomials
from sage.all import magma, prime_powers, vector, ZZ, matrix


def verify_norm(chain, polynomial, DD):
	"""
	Given a manifold dirichlet_domain DD, a chain in its second homology, and an Alexander polynomial,
	this attempts to find a representative of the surface whose euler characteristic matches the Thurston Norm.
	"""
	triangulation, maps = DD.get_triangulation(True)
	F2 = maps[2]
	tri_chain = F2*chain
	assert (DD.B2()*chain).norm() == 0
	assert (triangulation.get_boundary_map(2)*tri_chain).norm() == 0

	# print(triangulation.get_boundary_map(2)*tri_chain)
	# print(triangulation.get_boundary_map(3))
	best_chain = optimize.optimal_chain(tri_chain, triangulation.get_boundary_map(3))
	assert (triangulation.get_boundary_map(2)*best_chain).norm() == 0
	faces = 0
	vertices = set()
	print(best_chain)
	for index, value in enumerate(best_chain):
		faces += value.abs()
		if value != 0:
			vertices = vertices.union(triangulation.simplices[2][index].boundary(0))
	vertices = len(vertices)
	assert faces % 2 == 0
	# print('faces:%s' % faces)
	euler = faces/2 - vertices
	neg_euler = -euler

	alex_norm = alexander_norm(chain, polynomial)
	print(neg_euler, alex_norm)


def alexander_norm(chain, polynomial):
	term_results = []
	for term in polynomial.monomials():
		term_results.append(apply_polynomial_term(chain, term, DD).abs())
	norm = max([a-b for a in term_results for b in term_results])
	return norm


def apply_polynomial_term(chain, term, DD):
	"""
	Given a manifold dirichlet_domain DD, a chain in its second homology, and an Alexander polynomial,
	this applies the Alexander polynomial on the chain.
	"""
	H1_basis = DD.free_dual_H1_basis
	exps = term.exponents()[0]
	# print(term, H1_basis, exps)
	assert len(basis) == term.parent().ngens()
	if not hasattr(exps, '__getitem__'):
		exps = [exps]
	term_chain = vector(ZZ, exps)*matrix(H1_basis)
	# print(term_chain.dot_product(chain))
	return term_chain.dot_product(chain)


def thurston_norm(DD):
	"""
	Returns the thurston norm ball of the given manifold
	"""
	if len(DD.free_dual_H1_basis) == 1:
		basis = DD.B2().right_kernel().basis()
		assert len(basis) == 1
		chain = basis[0]


def get_torsions(DD, num_homs=None):
	rep_size = 1000
	G = DD.dual_fundamental_group()
	magmaG = rep_theory.get_magma_group(G)
	tic = time.perf_counter()
	for n in prime_powers(1000):
		homs = permutation_groups.sage_group_to_PGL2_through_magma(G, n, num_homs,False)
		sl_reps = []
		for hom in homs:
			hom = [m.transpose() for m in hom]
			representation_theory.check_pgl_rep(hom, G)
			hom = representation_theory.lift_PGL2_to_PSL2(hom)
			hom = representation_theory.fast_lift_SL2_simple_representation(hom, G)
			if hom:
				sl_reps.append(hom)
		if len(sl_reps) > 0:
			break
	toc = time.perf_counter()
	rep_time = toc - tic
	tic = time.perf_counter()
	torsions = []
	for rep in sl_reps:
		face_mapping = [None]*len(rep)*2
		face_mapping[0::2] = rep[:]
		face_mapping[1::2] = [mat.inverse() for mat in rep]
		phi = rep_theory.phi_from_face_mapping(face_mapping)
		ring = rep[0].base_ring()
		poly = DD.exact_torsion_polynomial(phi, ring, 2)
		torsions.append(poly)
	toc = time.perf_counter()
	torsion_time = toc - tic
	returns = {"torsions": torsions, "representations": sl_reps}
	returns['rep_size'] = rep_size
	returns["rep_time"] = rep_time
	returns["torsion_time"] = torsion_time
	if DD.dual_free_abelianization_ring().ngens() == 1:
		degrees = [tor.degree() for tor in torsions]
		max_degree = max(degrees)
		max_degree_index = degrees.index(max_degree)
		returns["max_degree"] = max_degree
		returns["max_degree_index"] = max_degree_index
	return returns


if __name__ == '__main__':
	import snappy
	for i in range(30):
		M = snappy.OrientableClosedCensus(betti=1)[i]
		DD = tw.TwistableDomain(M.dirichlet_domain())
		results = get_torsions(DD, 1)
		# print(results)
		assert len(DD.H2_basis) == 1
		basis = DD.H2_basis
		for vec in basis:
			assert (DD.B2()*vec).norm() == 0
		chain = basis[0]
		polynomial = results['torsions'][0]
		print(polynomial)
		print(M.alexander_polynomial())
		verify_norm(chain, polynomial, DD)
	# chain = DD.free_dual_H1_basis[1]
	# verify_norm(chain, results['torsions'][0], DD)