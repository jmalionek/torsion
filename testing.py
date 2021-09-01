import pickle
import random
import time

import networkx as nx
import snappy
from matplotlib import pyplot as plt
from sage.all import RR, CC, ZZ, GF
from snappy.snap import polished_reps as reps

import d_domain
import geometry
import representation_theory
import torsion_poly
from examples import random_closed_manifold
from twistable_revamp import TwistableDomain, HolonomyElement, fox_deriv, \
	find_face
from representation_theory import equal_matrices, is_nonprojective_representation, lift_projective_SL2C_representation, \
	fast_lift_SL2C_representation, phi_from_face_mapping
from cellulation import Alphabet, simplifiable


def test_boundaries(D):
	DD = TwistableDomain(D)
	NathanD = d_domain.FundamentalDomain(D)
	print('Me B1\n{0}'.format(DD.B1()))
	print('Nathan B1\n{0}'.format(NathanD.B1()))
	print('Me B2\n{0}'.format(DD.B2(False)))
	print('Nathan B2\n{0}'.format(NathanD.B2()))
	print('Me d squared\n{0}'.format(DD.B1() * DD.B2(False)))
	print('Nathan d squared\n{0}'.format(NathanD.B1() * NathanD.B2()))
	print('Me B2 smith form\n{0}'.format(DD.B2().smith_form()[0]))
	print('Nathan B2 smith form\n{0}'.format(NathanD.B2().smith_form()[0]))
	print('Me homology\n{0}'.format(DD.homology_chain_complex().homology()))
	print('Nathan homology\n{0}'.format(NathanD.homology_chain_complex().homology()))


def test_fundamental_group(D):
	torsion_poly.enhance_domain(D)
	# print(torsion_poly.get_relations(D,False))
	# print([hol.as_face_list() for hol in DD.get_dual_relations()])
	for i in range(10):
		D = random.choice(snappy.OrientableClosedCensus).dirichlet_domain()
		DD = TwistableDomain(D)
		torsion_poly.enhance_domain(D)
		# print(DD.dual_fundamental_group().abelian_invariants())
		print(M.homology())
		assert torsion_poly.sage_fundamental_group(D,
									False).abelian_invariants() == DD.dual_fundamental_group().abelian_invariants()


def test_dual_boundaries(D):
	DD = TwistableDomain(D)
	NathanD = d_domain.FundamentalDomain(D)
	print('Me dual B1 \n{0}'.format(DD.dualB1()))
	print('Nathan B3 \n{0}'.format(NathanD.B3()))
	print('Me dual B2 \n{0}'.format(DD.dualB2()))
	print('Nathan B2 \n{0}'.format(NathanD.B2()))
	print('Me dual B2 smith form\n{0}'.format(DD.dualB2().smith_form()[0]))
	print('Nathan B2 smith form\n{0}'.format(NathanD.B2().smith_form()[0]))
	print('Me dual B3 \n{0}'.format(DD.dualB3()))
	print('Nathan B1 \n{0}'.format(NathanD.B1()))
	print('Me dual B3 smith fom \n{0}'.format(DD.dualB3().smith_form()[0]))
	print('Nathan B1 smith form\n{0}'.format(NathanD.B1().smith_form()[0]))
	print('Me dsquared \n{0}'.format(DD.dualB2() * DD.dualB3()))
	for i in range(10):
		D = random.choice(snappy.OrientableClosedCensus).dirichlet_domain()
		DD = TwistableDomain(D)
		NathanD = d_domain.FundamentalDomain(D)
		assert (equal_matrices(DD.dualB2().smith_form()[0].transpose(), NathanD.B2().smith_form()[0]))
		assert (equal_matrices(DD.dualB3().smith_form()[0].transpose(), NathanD.B1().smith_form()[0]))
		assert (equal_matrices(DD.dualB2() * DD.dualB3(), 0))
		print('{0} tests good'.format(i + 1))


def test_reduced_boundaries(D, extended=True):
	DD = TwistableDomain(D)
	NathanD = d_domain.FundamentalDomain(D)
	print('Me reduced dual B2 \n{0}'.format(DD.reduced_dualB2()))
	print('Nathan B2 \n{0}'.format(NathanD.B2()))
	print('Me reduced dual B2 smith form\n{0}'.format(DD.reduced_dualB2().smith_form()[0]))
	print('Nathan B2 smith form\n{0}'.format(NathanD.B2().smith_form()[0]))
	print('Me reduced dual B3 \n{0}'.format(DD.reduced_dualB3()))
	print('Nathan B1 \n{0}'.format(NathanD.B1()))
	print('Me reduced_dual B3 smith fom \n{0}'.format(DD.reduced_dualB3().smith_form()[0]))
	print('Nathan B1 smith form\n{0}'.format(NathanD.B1().smith_form()[0]))
	print('Me reduced dual B2*B3 \n{0}'.format(DD.reduced_dualB2() * DD.reduced_dualB3()))
	print('Me reduced dual B1*B2 \n{0}'.format(DD.dualB1() * DD.reduced_dualB2()))
	if extended:
		for i in range(10):
			D = random.choice(snappy.OrientableClosedCensus).dirichlet_domain()
			DD = TwistableDomain(D)
			NathanD = d_domain.FundamentalDomain(D)
			assert DD.reduced_dualB2().smith_form()[0].diagonal(), NathanD.B2().smith_form()[0].diagonal()
			assert DD.reduced_dualB3().smith_form()[0].diagonal(), NathanD.B1().smith_form()[0].diagonal()
			assert equal_matrices(DD.dualB2() * DD.dualB3(), 0)
			print('{0} tests good'.format(i + 1))


def save_graphs(D, string):
	DD = TwistableDomain(D)
	plt.subplot(121)
	nx.draw_planar(DD.orbit_digraph)
	# plt.savefig('./pictures/' + string + '_orbit_digraph.png')
	plt.subplot(122)
	nx.draw_planar(DD.digraph, with_labes=True)
	plt.savefig('./pictures/' + string + '_digraphs.png')


def test_graphs(D):
	DD = TwistableDomain(D)
	# DD.orbit_digraph.plot(edge_labels = True).save('closedcensus_0_orbit_digraph.png')
	# DD.orbit_graph.plot(edge_labels = True).save('closedcensus_0_orbit_graph.png')
	print('spanning tree {0}'.format([str(edge) for edge in DD.spanning_tree]))
	print('essential edges {0}'.format([str(edge) for edge in DD.essential_edge_orbits]))
	path = DD.shortest_path_in_orbit_tree(DD.vertex_orbits[0], DD.vertex_orbits[-1], report_vertices=True)
	print('orbit path {0}'.format([tuple(str(el) for el in edge) for edge in path]))
	path_lift = DD.path_lift([el[2] for el in path], DD.vertex_orbits[0].preferred, True)
	print('lift edges {0}'.format([str(edge) for edge in path_lift[1]]))
	print('lift vertices {0}'.format([str(vertex) for vertex in path_lift[0]]))


def test_twisted_boundaries(D):
	DD = TwistableDomain(D)
	phi = phi_from_face_mapping(DD.pairing_matrices)
	DD.check_representation(phi)
	# ~ def phi(hol):
	# ~ sign = 1 if i <0 else 0
	# ~ i = 2*(abs(i)-1)+sign
	# ~ return D.pairing_matrices()[i]
	print('d1*d2' + '\n' * 4)
	print((DD.dualB1(phi=phi, ring=RR, dimension=4) * DD.dualB2(phi=phi, ring=RR, dimension=4)).n(digits=3))
	print('d2*d3' + '\n' * 4)
	print((DD.dualB2(phi=phi, ring=RR, dimension=4) * DD.dualB3(phi=phi, ring=RR, dimension=4)).n(digits=3))
	print('reduced d1*d2' + '\n' * 4)
	print((DD.dualB1(phi=phi, ring=RR, dimension=4) * DD.reduced_dualB2(phi=phi, ring=RR, dimension=4)).n(digits=3))
	print('reduced d2*d3' + '\n' * 4)
	print((DD.reduced_dualB2(phi=phi, ring=RR, dimension=4) * DD.reduced_dualB3(phi=phi, ring=RR, dimension=4)).n(
		digits=3))


def test_twisted_boundaries_moebius(D):
	DD = TwistableDomain(D)
	phi = phi_from_face_mapping(DD.moebius_transformations)
	DD.check_representation(phi)
	# ~ def phi(hol):
	# ~ sign = 1 if i <0 else 0
	# ~ i = 2*(abs(i)-1)+sign
	# ~ return D.pairing_matrices()[i]
	print('d1*d2' + '\n' * 4)
	print((DD.dualB1(phi=phi, ring=CC, dimension=2) * DD.dualB2(phi=phi, ring=CC, dimension=2)).n(digits=3))
	print('d2*d3' + '\n' * 4)
	print((DD.dualB2(phi=phi, ring=CC, dimension=2) * DD.dualB3(phi=phi, ring=CC, dimension=2)).n(digits=3))
	print('reduced d1*d2' + '\n' * 4)
	print((DD.dualB1(phi=phi, ring=CC, dimension=2) * DD.reduced_dualB2(phi=phi, ring=CC, dimension=2)).n(digits=3))
	print('reduced d2*d3' + '\n' * 4)
	print((DD.reduced_dualB2(phi=phi, ring=CC, dimension=2) * DD.reduced_dualB3(phi=phi, ring=CC, dimension=2)).n(
		digits=3))


def test_abelianization(manifold):
	D = manifold.dirichlet_domain()
	DD = TwistableDomain(D)
	print(DD.fundamental_group_abelianization())
	print(manifold.homology())
	phi = DD.map_to_dual_abelianization()
	print('Most of these should not be trivial')
	for generator in DD.all_holonomy:
		print(phi(generator))
	print('these (the orders of the relations pushed through the abelian map) should be 1')
	for relation in DD.get_dual_relations():
		print(phi(relation).order())
	print('These check that the abelianization map is a homomorphism on 10 random pairs of generators')
	print('The result should be the identity')
	for i in range(10):
		a = random.choice(DD.all_holonomy)
		b = random.choice(DD.all_holonomy)
		print(phi(a.compose(b)).inverse() * phi(a) * phi(b))
	print('These check that the free abelianization and the group ring of the free abelianization work')
	print('The first one in each tuple is the ablianization, the second is the free abelianization, ')
	print('the last is the free abelianization ring')
	free_ab = DD.map_to_dual_free_abelianization()
	free_ab_ring = DD.map_to_free_abelianization_ring()

	for i in range(10):
		a = random.choice(DD.all_holonomy)
		print((phi(a), free_ab(a), free_ab_ring(a)))


def test_boundaries_abelianized_group_ring(D):
	DD = TwistableDomain(D)
	ring = DD.dual_abelianization_ring()
	phi = DD.map_to_dual_abelianization_ring()
	group = DD.dual_fundamental_group()
	print('Images of generators are:')
	ims = []
	ims2 = []
	for i in range(len(DD.face_orbits)):
		ims.append((group([i + 1]), phi(HolonomyElement(face_list=[2 * i]))))
		ims2.append((group(DD.holonomy_generators[i].holonomy), phi(DD.holonomy_generators[i])))
	print(ims)
	print(ims2)
	identity = ring(1)
	b1 = DD.dualB1(phi=phi, ring=ring, identity=identity)
	b2 = DD.dualB2(phi=phi, ring=ring, identity=identity)
	b3 = DD.dualB3(phi=phi, ring=ring, identity=identity)
	print('Me dual B1 \n{0}'.format(b1))
	print('Me dual B2 \n{0}'.format(b2))
	print('Me dual B3 \n{0}'.format(b3))
	print('B1*B2\n{0}'.format(b1 * b2))
	print('B2*B3\n{0}'.format(b2 * b3))

	reducedb2 = DD.reduced_dualB2(phi=phi, ring=ring, identity=identity)
	reducedb3 = DD.reduced_dualB3(phi=phi, ring=ring, identity=identity)
	print('Me reduced dual B2 \n{0}'.format(reducedb2))
	print('Me reduced dual B3 \n{0}'.format(reducedb3))
	print('B1*reducedB2\n{0}'.format(b1 * reducedb2))
	print('reducedB2*reducedB3\n{0}'.format(reducedb2 * reducedb3))


def three_torus_testing():
	D = examples.ThreeTorusStructue()
	DD = TwistableDomain(D)
	ring = DD.dual_abelianization_ring()
	phi = DD.map_to_dual_abelianization_ring()
	identity = ring(1)
	b1 = DD.dualB1(phi=phi, ring=ring, identity=identity)
	b2 = DD.dualB2(phi=phi, ring=ring, identity=identity)
	b3 = DD.dualB3(phi=phi, ring=ring, identity=identity)
	print([str(rel) for rel in DD.get_dual_relations()])
	print(b1.transpose())
	print(b2)
	print(b3)
	print((b1 * b2))
	print((b2 * b3))


def test_noncommutative_group_ring_genus2():
	G = FreeGroup(4, 'abcd')
	A = G.algebra(ZZ)

	def phi(hol):
		return A(G(hol.holonomy))

	print('next line should be commutator of a and b')
	print(phi(HolonomyElement([1, 2, -1, -2])))
	b2 = []
	relation = HolonomyElement([4, -3, -4, 3, 2, -1, -2, 1])
	print('relation:{0}'.format(A(G(relation.holonomy))))
	for i in range(4):
		b2.append(fox_deriv(relation, i + 1, phi))
	b1 = []
	for i in range(4):
		b1.append(A(G(1)) - A(G([-i - 1])))
	print('b2\n{0}'.format(b2))
	print('b1\n{0}'.format(b1))
	b_squared = 0
	for i in range(4):
		b_squared += b1[i] * b2[i]
	print('composition\n{0}'.format(b_squared))


def test_noncommutative_group_ring(D):
	DD = TwistableDomain(D)
	print([str(x) for x in DD.get_dual_relations()])
	print([(x.index, str(x)) for x in DD.vertices])
	print([(x.index, str(x), '{0}->{1}'.format(x.tail.index, x.head.index)) for x in DD.edges])
	G = FreeGroup(len(DD.face_orbits))
	A = G.algebra(ZZ)

	def phi(hol):
		return A(G(hol.holonomy))

	num_vertices = len(DD.vertex_orbits)
	num_edges = len(DD.edge_orbits)
	num_faces = len(DD.face_orbits)

	print('\n\nb1\n\n')
	d1 = DD.dualB1(phi=phi, ring=A, as_list=True)
	b1 = matrix(A, 1, num_faces, 0)
	for i in range(num_faces):
		b1[0, i] = d1[i]
	print(b1)

	rd2 = DD.reduced_dualB2(phi=phi, ring=A, as_list=True)
	# print(rd2)

	# In unreduced, second is num_edges (probably)
	rb2 = matrix(A, num_faces, num_faces, 0)
	for i in range(num_faces):
		for j in range(num_faces):
			rb2[i, j] = rd2[i * num_faces + j]
	# print(DD.reduced_dualB2())
	print('\n\nreduced b2\n\n')
	print(rb2)

	d2 = DD.dualB2(phi=phi, ring=A, as_list=True)
	# print(rd2)

	# In unreduced, second is num_edges (probably)
	b2 = matrix(A, num_faces, num_edges, 0)
	for i in range(num_faces):
		for j in range(num_edges):
			b2[i, j] = d2[i * num_faces + j]
	# print(DD.reduced_dualB2())
	print('\n\nb2\n\n')
	print(b2)

	d3 = DD.dualB3(phi=phi, ring=A, as_list=True)

	print('\n\nb1*reduced b2\n\n')
	print(b1 * rb2)

	print('\n\nb3\n\n')
	b3 = matrix(A, num_edges, num_vertices, 0).transpose()
	# b3 = matrix(A,num_vertices,num_edges,d3).transpose()
	for i in range(num_vertices):
		b3[i] = d3[i]
	b3 = b3.transpose()

	rd3 = DD.reduced_dualB3(phi=phi, ring=A, as_list=True)
	rb3 = matrix(A, len(DD.essential_edge_orbits), 1, 0)
	for i in range(len(DD.essential_edge_orbits)):
		rb3[i, 0] = rd3[i]
	# print(rd3)
	print(b3)

	print('\n\nreduced b3\n\n')
	print(rb3)
	# ~ rb3 = matrix(A,num_edges,num_vertices,0)
	# ~ for i in range(num_faces):
	# ~ for j in range(num_faces):
	# ~ rb2[i,j] = rd2[i*num_faces+j]
	print('\n\ncomposition of reduced b2 and reduced b3 (in matrix multiplication order order)\n\n')
	print(rb2 * rb3)

	print('\n\ncomposition of b2 and b3 (in matrix multiplication order order)\n\n')
	print(b2 * b3)


def test_Seifert_Weber():
	D = examples.SeifertWeberStructure()
	# D = examples.snappySW
	DD = TwistableDomain(D)
	print([str(x) for x in DD.get_dual_relations()])
	print([(x.index, str(x)) for x in DD.vertices])
	G = FreeGroup(len(DD.face_orbits))
	A = G.algebra(ZZ)

	def phi(hol):
		return A(G(hol.holonomy))

	num_vertices = len(DD.vertex_orbits)
	num_edges = len(DD.edge_orbits)
	num_faces = len(DD.face_orbits)

	print('\n\nb1\n\n')
	d1 = DD.dualB1(phi=phi, ring=A, as_list=True)
	b1 = matrix(A, 1, num_faces, 0)
	for i in range(num_faces):
		b1[0, i] = d1[i]
	print(b1)

	rd2 = DD.reduced_dualB2(phi=phi, ring=A, as_list=True)
	# print(rd2)

	# In unreduced, second is num_edges (probably)
	rb2 = matrix(A, num_faces, num_faces, 0)
	for i in range(num_faces):
		for j in range(num_faces):
			rb2[i, j] = rd2[i * num_faces + j]
	# print(DD.reduced_dualB2())
	print('\n\nb1*reduced b2\n\n')
	print(rb2)
	d3 = DD.dualB3(phi=phi, ring=A, as_list=True)

	print('\n\nb1*b2\n\n')
	print(b1 * rb2)

	print('\n\nb3\n\n')
	b3 = matrix(A, num_edges, num_vertices, 0).transpose()
	# b3 = matrix(A,num_vertices,num_edges,d3).transpose()
	for i in range(num_vertices):
		b3[i] = d3[i]
	b3 = b3.transpose()

	rd3 = DD.reduced_dualB3(phi=phi, ring=A, as_list=True)
	rb3 = matrix(A, len(DD.essential_edge_orbits), 1, 0)
	for i in range(len(DD.essential_edge_orbits)):
		rb3[i, 0] = rd3[i]
	# print(rd3)
	print(b3)

	print('\n\nreduced b3\n\n')
	print(rb3)
	# ~ rb3 = matrix(A,num_edges,num_vertices,0)
	# ~ for i in range(num_faces):
	# ~ for j in range(num_faces):
	# ~ rb2[i,j] = rd2[i*num_faces+j]
	print('\n\ncomposition of reduced b2 and reduced b3 (in matrix multiplication order order)\n\n')
	print(rb2 * rb3)


def test_holonomy_matrices():
	# manifold = snappy.OrientableClosedCensus[0]
	D = examples.snappySWDomain
	NathanD = d_domain.FundamentalDomain(D)
	DD = TwistableDomain(D)

	# for i in range(len(DD.vertices)):
	# 	print(DD.vertices[i].coords)
	# 	print(NathanD.vertices[i])
	J = diagonal_matrix([-1, 1, 1, 1])
	for mat in DD.pairing_matrices:
		print(mat*J*mat.transpose())

	for i in range(len(DD.face_list)):
		print([vertex.index for vertex in DD.face_list[i].vertices])
		print(NathanD.faces[i].indices)
		print(HolonomyElement(face_list=[i], domain=DD).matrix(), DD.pairing_matrices[i])

	for i, face_dict in enumerate(DD.D.face_list()):
		pairing_matrix = HolonomyElement(face_list=[i], domain=DD).matrix()
		print('NEW FACE')
		print(face_dict['vertex_indices'], face_dict['vertex_image_indices'])
		nathan_face = find_face(NathanD, face_dict['vertex_indices'])
		print('nathan vertex indices')
		print(nathan_face.indices)
		print('nathan vertex coords')
		print(nathan_face.vertices)
		print('nathan paired vertex indices')
		print(nathan_face.paired_face.indices)
		print('nathan paired vertex coords')
		print(nathan_face.paired_face.vertices)
		print('nathan pairing matrix')
		print(nathan_face.pairing_matrix)
		print('pairing matrix')
		print(pairing_matrix)
		for j, vertex_index in enumerate(face_dict['vertex_indices']):
			original_vertex = DD.vertices[vertex_index]
			paired_vertex = DD.vertices[face_dict['vertex_image_indices'][j]]
			print(original_vertex.index, paired_vertex.index)
			print(original_vertex.holonomy, paired_vertex.holonomy)
			print('original vertex coords')
			print(original_vertex.coords)
			print('vertex coordinates from snappy versus calculated holonomy coordinates')
			print(paired_vertex.coords, pairing_matrix*original_vertex.coords)
			print('matrix given by snappy versus matrix calculated by combining holonomies.')
			print(pairing_matrix)
			print(paired_vertex.holonomy.matrix()*original_vertex.holonomy.inverse().matrix())


def test_individual_holonomy(D=None):
	if D is None:
		D = examples.snappySWDomain
	DD = TwistableDomain(D)
	for vertex in DD.vertices:
		# print(vertex.orbit.preferred.coords)
		# print(vertex.holonomy.matrix())
		print(vertex.coords)
		print(vertex.holonomy.matrix()*vertex.orbit.preferred.coords)
		print()


def test_lift():
	D = snappy.Manifold('m160(-3, 2)').dirichlet_domain()
	D = random.choice(snappy.OrientableClosedCensus(betti=2)).dirichlet_domain()
	DD = TwistableDomain(D, use_matrix_data=False)
	matrices = [None]*len(D.pairing_matrices())
	matrices[::2] = [geometry.O31_to_Moebius(mat) for mat in D.pairing_matrices()[::2]]
	matrices[1::2] = [matrix.inverse() for matrix in matrices[0::2]]
	relations = DD.get_dual_relations(reduced=True)
	alpha_relations = [[Alphabet[i] for i in hol.holonomy] for hol in relations]
	alpha_gens = []
	print(alpha_relations)
	for rel in alpha_relations:
		for letter in rel:
			if letter.lower() not in alpha_gens:
				alpha_gens.append(letter.lower())
	alpha_gens.sort()
	print(alpha_gens)
	Nathan_rep = reps.MatrixRepresentation(alpha_gens, alpha_relations, matrices[::2])
	my_rep = lift_projective_SL2C_representation(matrices, relations)
	print(is_nonprojective_representation(my_rep, relations))
	print(Nathan_rep.is_projective_representation())


def test_torsion_polynomial():
	manifold = snappy.OrientableClosedCensus(betti=2)[0]
	manifold = snappy.ManifoldHP(manifold)
	D = manifold.dirichlet_domain()
	DD = TwistableDomain(D)
	print(DD.torsion_polynomial())
	print(manifold.alexander_polynomial())


def calculate_torsion_polynomial_from_positive_betti_census(index):
	if index < 127:
		manifold = snappy.OrientableClosedCensus(betti=1)[index]
	elif index == 127:
		manifold = snappy.OrientableClosedCensus(betti=2)[0]
	else:
		raise RuntimeError('index too high, must be 127 or less')
	manifold = snappy.ManifoldHP(manifold)
	D = manifold.dirichlet_domain()
	DD = TwistableDomain(D)
	return DD.torsion_polynomial()


def test_torsion_vs_alex():
	for i in range(100):
		manifold = snappy.OrientableClosedCensus(betti=1)[i]
		manifold = snappy.ManifoldHP(manifold)
		D = manifold.dirichlet_domain()
		DD = TwistableDomain(D)
		print('index:%s' % i)
		print(DD.torsion_polynomial())
		print(manifold.alexander_polynomial())
		print('\n')


def calculate_random_torsion_polynomials(num_crossings, num_components):
	with open('/home/joseph/Documents/Math/Research/torsion/files/random_manifolds.pickle', 'rb') as manifold_file:
		manifold_list = pickle.load(manifold_file)
	try:
		while True:
			manifold = random_closed_manifold(num_crossings, num_components)
			D = manifold.dirichlet_domain()
			DD = TwistableDomain(D)
			print('started calculating torsion polynomial for domain with %s 1-cells...' % len(DD.holonomy_generators))
			tic = time.perf_counter()
			polynomial = DD.torsion_polynomial()
			toc = time.perf_counter()
			print('...finished calculating, took %s second' % toc - tic)
			data = {}
			data['time'] = toc-tic
			data['manifold'] = manifold
			data['polynomial'] = polynomial
			manifold_list.append(data)
	finally:
		with open('/home/joseph/Documents/Math/Research/torsion/files/random_manifolds.pickle', 'wb') as manifold_file:
			pickle.dump(manifold_list, manifold_file)


def test_random_multivariate_torsion_polynomial(num_crossings, num_components=2):
	manifold = random_closed_manifold(num_crossings, num_components)
	D = manifold.dirichlet_domain()
	print('successfully constructed Dirichlet Domain')
	DD = TwistableDomain(D)
	print('Successfully constructed specialized Dirichlet Domain')
	print('number of 1-cells: %s' % len(DD.holonomy_generators))
	tic = time.perf_counter()
	print(DD.torsion_polynomial(time_determinant=True))
	toc = time.perf_counter()
	print('It took %s seconds to calculate the torsion polynomial' % (toc - tic))
	print(manifold.alexander_polynomial())


def test_finite_covers():
	manifold = random.choice(snappy.OrientableClosedCensus(betti=1))
	print(str(manifold))
	i = 3
	print('degree:%s cover' % i)
	cover = manifold.covers(i)[0]
	cover = cover.high_precision()
	print('num tetrahedra:%s' % cover.num_tetrahedra())
	D = cover.dirichlet_domain()
	DD = TwistableDomain(D)
	print(cover.volume())
	print(cover.alexander_polynomial())
	print(DD.torsion_polynomial())


def test_fast_lift():
	manifold = snappy.OrientableClosedCensus(betti=2)[0]
	manifold = snappy.ManifoldHP(manifold)
	D = manifold.dirichlet_domain()
	DD = TwistableDomain(D)
	matrices = [None] * len(D.pairing_matrices())
	matrices[::2] = [geometry.O31_to_Moebius(mat, 212) for mat in D.pairing_matrices()[::2]]
	matrices[1::2] = [matrix.inverse() for matrix in matrices[0::2]]

	new_mats = fast_lift_SL2C_representation(matrices, DD.get_dual_relations(False))
	print(is_nonprojective_representation(matrices, DD.get_dual_relations(reduced=False)))
	print(is_nonprojective_representation(new_mats, DD.get_dual_relations(reduced=False)))


def debug_determinant(index=8):
	manifold = snappy.OrientableClosedCensus(betti=1)[index]
	manifold = snappy.ManifoldHP(manifold)
	D = manifold.dirichlet_domain()
	DD = TwistableDomain(D)
	return DD.torsion_polynomial()


def profile_torsion():
	manifold = snappy.OrientableClosedCensus(betti=2)[0]
	manifold = snappy.ManifoldHP(manifold)
	prof = cProfile.Profile()
	stats = pstats.Stats(prof)
	D = manifold.dirichlet_domain()
	prof.enable()
	DD = TwistableDomain(D)
	DD.torsion_polynomial()
	prof.disable()
	stats.sort_stats('cumulative')
	stats.print_stats(40)


def calculate_all_census_polynomials():
	with open('/home/joseph/Documents/Math/Research/torsion/files/census_polynomials.pickle', 'rb') as poly_file:
		polynomial_list = pickle.load(poly_file)
	index = -1
	for i in range(len(polynomial_list)):
		entry = polynomial_list[i]
		if entry is not None and entry != 'error':
			index = i
	index += 1
	try:
		while index < 128:
			polynomial = calculate_torsion_polynomial_from_positive_betti_census(index)
			polynomial_list[index] = polynomial
			print('Calculated manifold %s' % index)
			index += 1
	except KeyboardInterrupt as e:
		pass
	except RuntimeError as e:
		polynomial_list[index] = 'error'
	finally:
		with open('/home/joseph/Documents/Math/Research/torsion/files/census_polynomials.pickle', 'wb') as poly_file:
			pickle.dump(polynomial_list, poly_file)


def test_simplifiable():
	from examples import random_closed_manifold
	import twistable_revamp
	# M = random_closed_manifold(50, 2)
	# print("found manifold")
	for i in range(len(snappy.OrientableClosedCensus)):
		try:
			M = snappy.OrientableClosedCensus[i]
			DD = twistable_revamp.TwistableDomain(M.dirichlet_domain())
			simplifications = simplifiable(DD)
			if len(simplifications) > 0:
				print(i, simplifications)
			print("\rSimplified %s" % i, end="")
		except RuntimeError as e:
			pass
	print("Done")


def test_finite_torsion():
	import representation_theory as rep_theory
	M = random.choice(snappy.OrientableClosedCensus(betti=2))
	print(M)
	DD = TwistableDomain(M.dirichlet_domain())
	good_rep = False
	ngens = DD.dual_fundamental_group().simplification_isomorphism().codomain().ngens()
	print("Finding a representation on {0} generators".format(ngens))
	for prime in [2, 3, 5, 7, 11]:
		reps, simp_reps = rep_theory.get_SL2p_representations2(DD.dual_fundamental_group(), prime, True, True)
		if len(reps) > 0:
			print("Representation over Z%s" % prime)
			ring = GF(prime)
			good_rep = True
			break
		else:
			print("No reps in Z/{0}".format(prime))
	if good_rep:
		index = random.randint(0, len(reps)-1)
		chosen_rep = reps[index]
		for thing in simp_reps[index]:
			print(thing)
		inverses = [mat.inverse() for mat in chosen_rep]
		rep = [None]*len(chosen_rep)*2
		rep[0::2] = chosen_rep
		rep[1::2] = inverses
		assert rep_theory.is_exact_representation(rep, DD.get_dual_relations())
		# print(rep)
		tor = DD.exact_torsion_polynomial(phi=phi_from_face_mapping(rep), base_ring=ring, dimension=2)
		print("torsion polynomial:")
		print(tor)
		print("alexander polynomial:")
		print(M.alexander_polynomial())
	else:
		print("no good rep found")


def test_finite_torsion_arbitrary_crossings(num_crossings, betti):
	import representation_theory as rep_theory
	tic = time.perf_counter()
	M = random_closed_manifold(num_crossings, betti)
	toc = time.perf_counter()
	print("It took {0} seconds to find a manifold which is the exterior of a knot with {1} crossings".format(
		toc-tic, len(M.link().crossings)))
	DD = TwistableDomain(M.dirichlet_domain())
	good_rep = False
	ngens = DD.dual_fundamental_group().simplification_isomorphism().codomain().ngens()
	print("Finding a representation on {0} generators".format(ngens))
	for prime in [2, 3, 5]:
		reps, simp_reps = rep_theory.get_SL2p_representations2(DD.dual_fundamental_group(), prime, True, True)
		if len(reps) > 0:
			print("Representation over Z%s" % prime)
			ring = GF(prime)
			good_rep = True
			break
		else:
			print("No reps in Z/{0}".format(prime))
	if good_rep:

		index = random.randint(0, len(reps)-1)
		chosen_rep = reps[index]
		print('RIGHT BEFORE')
		for thing in simp_reps[index]:
			print(thing)
		print('RIGHT NOW')
		inverses = [mat.inverse() for mat in chosen_rep]
		rep = [None] * len(chosen_rep) * 2
		rep[0::2] = chosen_rep
		rep[1::2] = inverses
		assert rep_theory.is_exact_representation(rep, DD.get_dual_relations())
		# print(rep)
		tic = time.perf_counter()
		tor = DD.exact_torsion_polynomial(phi=phi_from_face_mapping(rep), base_ring=ring, dimension=2)
		toc = time.perf_counter()
		print("It took {0} seconds to calculate the torsion polynomial".format(toc-tic))
		print("torsion polynomial:")
		print(tor)
		print("alexander polynomial:")
		print(M.alexander_polynomial())
	else:
		print("no good rep found")


def test_matrix_generation(p):
	for i in range(p**3-p):
		mat = representation_theory.num_to_matrix2(i, p)
		print(mat)
		print(mat.det())


if __name__ == '__main__':
	import examples
	# M = snappy.Manifold('m037')
	# domain = M.dirichlet_domain()
	# test_holonomy_matrices()
	# M = snappy.OrientableClosedCensus[0]
	# M = snappy.Manifold('m160(-3, 2)')
	# M = random.choice(snappy.OrientableClosedCensus(betti=2))
	# M = random.choice(snappy.OrientableClosedCensus)
	# test_individual_holonomy(domain)
	# domain = examples.SeifertWeberStructure()
	# NathanD = d_domain.FundamentalDomain(D)
	# test_boundaries(D)
	# test_fundamental_group(D)
	# test_dual_boundaries(D)
	# test_graphs(D)
	# test_reduced_boundaries(D)
	# test_twisted_boundaries(domain)
	# save_graphs(examples.snappySWDomain, 'snappy_seif_vape_dodec')
	# save_snappySW_graphs()
	# test_boundaries_abelianized_group_ring(D)
	# test_boundaries_abelianized_group_ring(domain)
	# test_abelianization(M)
	# three_torus_testing()
	# test_noncommatative_group_ring_genus2()
	# test_noncommutative_group_ring(domain)
	# test_Seifert_Weber()
	# print(DD.B2().smith_form()[0]==(NathanD.B2().smith_form()[0]))
	# test_lift()
	# test_fast_lift()
	# test_torsion_polynomial()
	# test_finite_covers()
	# test_random_multivariate_torsion_polynomial(30, 2)
	# test_simplifiable()
	# calculate_random_torsion_polynomials(40, 2)
	# calculate_torsion_polynomial_from_census(0)
	# test_torsion_vs_alex()
	# test_twisted_boundaries_moebius(domain)
	# profile_torsion()
	test_finite_torsion()
	# test_finite_torsion_arbitrary_crossings(60, 1)
	# test_matrix_generation(5)
	# SEIFERT WEBER EXAMPLES
	test_SW = False
	if test_SW:
		test_Seifert_Weber()
		test_boundaries_abelianized_group_ring(D=examples.SeifertWeberStructure())
	test_this = False
	if test_this:
		test_twisted_boundaries(domain)
		test_noncommutative_group_ring(domain)
		test_boundaries_abelianized_group_ring(domain)

