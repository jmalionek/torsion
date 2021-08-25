import time

from sage.all import RR, ZZ, matrix, vector, ComplexField
from sage.all import ChainComplex, AbelianGroup, FreeGroup, LaurentPolynomialRing, PolynomialRing
import snappy
import networkx as nx
import geometry
import polynomials as poly

# noinspection SpellCheckingInspection
from cellulation import Vertex, VertexOrbit, Edge, EdgeOrbit, Face, FaceOrbit


# noinspection PyTypeChecker
from representation_theory import equal_matrices, is_nonprojective_representation, fast_lift_SL2C_representation, \
	phi_from_face_mapping


class TwistableDomain(object):

	def __init__(self, dirichlet_domain, use_matrix_data=True, precision=None):
		self.D = dirichlet_domain
		self.sage_dual_group = None
		self.sage_dual_group_ring = None
		self.abelianization = None
		self.abelianization_ring = None
		self.free_abelianization = None
		self.free_abelianization_ring = None
		self.pairing_matrices = None
		self.moebius_transformations = None
		if precision is None:
			if type(self.D) == snappy.DirichletDomainHP:
				self.precision = 212
			else:
				self.precision = 53
		self._setup_holonomy()
		self._setup_vertex_orbits()
		self._setup_edge_orbits()
		self._setup_cells()
		self._setup_edges()
		self._setup_faces()
		self._setup_graphs()
		if hasattr(self.D, 'pairing_matrices') and use_matrix_data:
			matrices = [None] * len(self.D.pairing_matrices())
			matrices[::2] = [geometry.O31_to_Moebius(mat, self.precision) for mat in self.D.pairing_matrices()[::2]]
			matrices[1::2] = [matrix.inverse() for matrix in matrices[0::2]]
			rels = self.get_dual_relations(reduced=True)
			mats = fast_lift_SL2C_representation(matrices, rels)
			self.moebius_transformations = mats
			self.pairing_matrices = self.D.pairing_matrices

	# ---------------------------SETUP-----------------------
	def _setup_holonomy(self):
		# Note that under the conventions of this program, the holonomy corresponding to the even faces
		# do not map to the opposite side, but do map the opposite (odd faced) side to the even face.
		self.holonomy_generators = []
		self.holonomy_inverse_generators = []
		self.all_holonomy = []
		for i, face in enumerate(self.D.face_list()):
			hol = HolonomyElement(face_list=[i], domain=self)
			if i % 2 == 0:
				self.holonomy_generators.append(hol)
			else:
				self.holonomy_inverse_generators.append(hol)
			self.all_holonomy.append(hol)

	# ~ def _setup_polyhedra(self):
	# ~ if self.D != None:
	# ~ self.polyhedra = []
	# ~ poly = Polyhedron(0)

	def _setup_vertex_orbits(self):
		num_orbits = max([vertex['vertex_class'] for vertex in self.D.vertex_list(True)]) + 1
		self.vertex_orbits = [None] * num_orbits
		self.vertices = [None] * len(self.D.vertex_list())
		for index, vertex_dict in enumerate(self.D.vertex_list(True)):
			orbit_index = vertex_dict['vertex_class']
			if self.vertex_orbits[orbit_index] is None:
				if 'position' in vertex_dict.keys():
					coords = vertex_dict['position']
				else:
					coords = None
				vertex = Vertex(index=index, holonomy=HolonomyElement([], domain=self),
				                coords=coords)
				orbit = VertexOrbit(preferred=vertex, index=orbit_index)
				orbit.add(vertex)
				self.vertices[index] = vertex
				self.vertex_orbits[orbit_index] = orbit

	def _setup_edge_orbits(self):
		num_orbits = max([edge['edge_class'] for edge in self.D.edge_list()]) + 1
		self.edge_orbits = [None] * num_orbits
		self.edges = [None] * len(self.D.edge_list())
		for index, edge_dict in enumerate(self.D.edge_list()):
			orbit_index = edge_dict['edge_class']
			if self.edge_orbits[orbit_index] is None:
				edge = Edge(index=index, holonomy=HolonomyElement([], domain=self))
				orbit = EdgeOrbit(preferred=edge, index=orbit_index)
				orbit.add(edge)
				self.edges[index] = edge
				self.edge_orbits[orbit_index] = orbit

	def _setup_cells(self):
		vertex_graph = nx.DiGraph()
		vertex_graph.add_nodes_from(range(len(self.vertices)))
		edge_graph = nx.DiGraph()
		edge_graph.add_nodes_from(range(len(self.edges)))
		for face_index, face_dict in enumerate(self.D.face_list()):
			vertex_mappings = list(zip(face_dict['vertex_indices'], face_dict['vertex_image_indices'],
								[{'face': face_index}]*len(face_dict['vertex_indices'])))
			edge_mappings = list(zip(face_dict['edge_indices'], face_dict['edge_image_indices'],
								[{'face': face_index}] * len(face_dict['edge_indices'])))
			vertex_graph.add_edges_from(vertex_mappings)
			edge_graph.add_edges_from(edge_mappings)
		# NOTE: We are taking the inverse of the element because we are using the convention that
		# even faces are oriented outwards, and so the holonomy pairing them to the opposite
		# face should be the inverse element
		for index, vertex in enumerate(self.vertices):
			if vertex is None:
				orbit_index = self.D.vertex_list(True)[index]['vertex_class']
				path = nx.shortest_path(vertex_graph, self.vertex_orbits[orbit_index].preferred.index, index)
				face_list = []
				for i in range(len(path) - 1):
					face_list.append(vertex_graph.edges[path[i], path[i + 1]]['face'])
				self.vertices[index] = Vertex(orbit=self.vertex_orbits[orbit_index],
				                              holonomy=HolonomyElement(face_list=face_list, domain=self).inverse(),
				                              index=index)
				if 'position' in self.D.vertex_list(True)[index].keys():
					self.vertices[index].set_coords(self.D.vertex_list()[index])

		for index, edge in enumerate(self.edges):
			if edge is None:
				orbit_index = self.D.edge_list()[index]['edge_class']
				path = nx.shortest_path(edge_graph, self.edge_orbits[orbit_index].preferred.index, index)
				face_list = []
				for i in range(len(path)-1):
					face_list.append(edge_graph.edges[path[i], path[i+1]]['face'])
				self.edges[index] = Edge(orbit=self.edge_orbits[orbit_index],
				                         holonomy=HolonomyElement(face_list=face_list, domain=self).inverse(),
				                         index=index)
		# checking that the new holonomies are the old holonomies
		# for i in range(len(self.vertices)):
		# 	assert self.vertices[i].holonomy == vertices[i].holonomy
		# for i in range(len(self.edges)):
		# 	assert self.edges[i].holonomy == edges[i].holonomy

	def _setup_edges(self):
		for index, edge_dict in enumerate(self.D.edge_list()):
			edge = self.edges[index]
			head = self.vertices[edge_dict['tip_vertex_index']]
			head.adjacent_edges.append(edge)
			if edge.orbit not in head.orbit.adjacent_edges:
				head.orbit.adjacent_edges.append(edge.orbit)
			tail = self.vertices[edge_dict['tail_vertex_index']]
			tail.adjacent_edges.append(edge)
			if edge.orbit not in tail.orbit.adjacent_edges:
				tail.orbit.adjacent_edges.append(edge.orbit)
			edge.tail = tail
			edge.orbit.tail = tail.orbit
			edge.head = head
			edge.orbit.head = head.orbit

	def _setup_faces(self):
		self.face_list = []
		self.face_orbits = []
		for i, face_dict in enumerate(self.D.face_list()):
			vertices = [self.vertices[index] for index in face_dict['vertex_indices']]
			edges = [self.edges[index] for index in face_dict['edge_indices']]
			paired_vertices = [self.vertices[index] for index in face_dict['vertex_image_indices']]
			paired_edges = [self.edges[index] for index in face_dict['edge_image_indices']]
			if i % 2 == 0:
				signs = face_dict['edge_orientations'][::-1]
				face = Face(None, HolonomyElement(face_list=[], domain=self), vertices[::-1],
							edges[::-1], paired_vertices[::-1],
							paired_edges[::-1], [x * (-1) for x in signs], index=i)
			# face = Face(None, HolonomyElement([]), vertices, edges, paired_vertices, paired_edges,
			# 			edge_orientations=signs, index=i)
			else:
				signs = face_dict['edge_orientations']
				# We want the holonomy to preserve the orientation of the cells
				# We work under the assumption that all 3 cells are oriented outward
				# i.e. the induced orientation on the faces follows a right hand rule
				face = Face(None, HolonomyElement([i], domain=self), vertices, edges,
				            paired_vertices, paired_edges,
				            edge_orientations=signs, index=i)
			# face = Face(None, HolonomyElement(face_list=[i]), vertices[::-1], edges[::-1], paired_vertices[::-1],
			# 			paired_edges[::-1], [x * (-1) for x in signs], index=i)
			self.face_list.append(face)
			for edge in edges:
				edge.adjacent_faces.append(face)
			if i % 2 == 0:
				orbit = FaceOrbit(face, [vertex.orbit for vertex in vertices], [edge.orbit for edge in edges], signs,
				                  int(i / 2))
				orbit.add(face)
				self.face_orbits.append(orbit)
				for edge in edges:
					edge.orbit.adjacent_faces.append(orbit)
			else:
				self.face_list[i - 1].paired_face = self.face_list[i]
				self.face_list[i].paired_face = self.face_list[i - 1]
				orbit = self.face_orbits[int((i - 1) / 2)]
				orbit.add(face)

	# -----------------------GRAPH THEORY-----------------------------------------

	# Make it so that the tree has all of the preferred vertices and edges
	# For the remaining edges, make it so that they are tree-adjacent
	# You can do this by choosing a preferred vertex of v0, then looking at all of the
	# orbit tree edges connected to that vertex, find which of those edges reps are connected
	# to the preferred vertex and then add the other end and so on...

	# Or try correcting the tree afterwards?

	def _setup_graphs(self):
		# Digraphs
		self.digraph = nx.MultiDiGraph()
		self.digraph.add_nodes_from(self.vertices)
		self.digraph.add_edges_from([(edge.tail, edge.head, {'data': edge}) for edge in self.edges])
		self.orbit_digraph = nx.MultiDiGraph()
		self.orbit_digraph.add_nodes_from(self.vertex_orbits)
		self.orbit_digraph.add_edges_from([(edge.tail, edge.head, {'data': edge}) for edge in self.edge_orbits])

		# Undirected graphs
		self.graph = nx.MultiGraph()
		self.graph.add_nodes_from(self.vertices)
		self.graph.add_edges_from([(edge.tail, edge.head, {'data': edge}) for edge in self.edges])
		self.orbit_graph = nx.MultiGraph()
		self.orbit_graph.add_nodes_from(self.vertex_orbits)
		self.orbit_graph.add_edges_from([(edge.tail, edge.head, {'data': edge}) for edge in self.edge_orbits])

		assert len(list(self.graph.edges)) == len(list(self.digraph.edges))
		assert len(list(self.orbit_graph.edges)) == len(list(self.orbit_digraph.edges))
		spanning_tree = list(nx.minimum_spanning_edges(self.orbit_graph, data=True))
		if len(spanning_tree) > 0:
			self.spanning_tree = [edge[3]['data'] for edge in spanning_tree]
			self.essential_edge_orbits = [edge for edge in self.edge_orbits if edge not in self.spanning_tree]
			self.spanning_tree_graph = nx.Graph()
			self.spanning_tree_graph.add_nodes_from(self.vertices)
			self.spanning_tree_graph.add_edges_from([(edge.tail, edge.head, {'data': edge}) for edge in self.spanning_tree])
		else:
			self.spanning_tree = []
			self.essential_edge_orbits = [edge for edge in self.edge_orbits]
			self.spanning_tree_graph = nx.Graph()
			self.spanning_tree_graph.add_node(self.vertices[0])

	def shortest_path_in_orbit_tree(self, v0, v1, report_vertices=False):
		vertex_path = nx.shortest_path(self.spanning_tree_graph, v0, v1)
		edge_path = []
		for i in range(len(vertex_path)-1):
			edge_path.append(self.spanning_tree_graph.edges[vertex_path[i], vertex_path[i+1]]['data'])
		if report_vertices:
			return vertex_path
		else:
			return edge_path

	# assumes that no edge in the vertex path has same head and tail
	@staticmethod
	def path_lift(edge_path, starting_vertex, report_vertices=True, report_edges=False):
		vertex = starting_vertex
		vertices = [vertex]
		edges = []
		for edge_orbit in edge_path:
			if vertex.orbit == edge_orbit.tail:
				edge = edge_orbit.lift(vertex, tail=True)
				vertex = edge.head
			elif vertex.orbit == edge_orbit.head:
				edge = edge_orbit.lift(vertex, head=True)
				vertex = edge.tail
			else:
				raise Exception('starting vertex is not on initial edge')
			edges.append(edge)
			vertices.append(vertex)
		if report_vertices and report_edges:
			return vertices, edges
		elif report_vertices and not report_edges:
			return vertices
		elif report_edges and not report_vertices:
			return edges
		else:
			return

	# ----------------------Fundamental Group-----------------------------
	# element 0 of the list is the first cell in the path of the boundary of a disk D
	# in the dual cellulation.

	def get_dual_relations(self, reduced=False):
		relations = []
		if reduced:
			edge_orbits = self.essential_edge_orbits
		else:
			edge_orbits = self.edge_orbits
		for orbit in edge_orbits:
			edge = orbit.preferred
			# determine face orientations with respect to the base polyhedron
			face0 = edge.adjacent_faces[0]
			face1 = edge.adjacent_faces[1]
			edge_orient_from_inside_face0 = face0.edge_sign(edge) * (-1) ** (face0.index % 2)
			edge_orient_from_inside_face1 = face1.edge_sign(edge) * (-1) ** (face1.index % 2)
			assert (edge_orient_from_inside_face0 != edge_orient_from_inside_face1)
			# ORIGINALLY ==
			if edge_orient_from_inside_face0 == 1:
				first_face = face0
			# last_face = face1
			else:
				first_face = face1
			# last_face = face0
			holonomy = HolonomyElement([], domain=self)
			current_face = first_face
			current_edge = edge
			nextface = current_face.paired_face
			nextedge = None
			while nextedge != edge:
				# ORIGINAL
				# holonomy = holonomy.compose(HolonomyElement(face_list = [current_face.index]))
				# NEW ONE (THIS ONE MAKES MORE SENSE)
				holonomy = HolonomyElement(face_list=holonomy.as_face_list()+[current_face.index],
										domain=self)
				nextedge = current_face.opposite_edge(current_edge)
				assert nextface in nextedge.adjacent_faces
				badindex = nextedge.adjacent_faces.index(nextface)
				assert len(nextedge.adjacent_faces) == 2
				goodindex = 1 - badindex
				current_face = nextedge.adjacent_faces[goodindex]
				current_edge = nextedge
				nextface = current_face.paired_face
			# holonomy = holonomy.compose(HolonomyElement(face_list = [current_face.index]))
			# ORIGINALLY HAD NO INVERSE
			relations.append(holonomy)
		# print('twistable {0}'.format([relation.holonomy for relation in relations]))
		return relations

	# returns a sage group object which is a presentation of the fundamental group of M
	# obtained by dualizing M
	def dual_fundamental_group(self):
		if self.sage_dual_group is None:
			F = FreeGroup(len(self.holonomy_generators))
			# ORIGINAL
			# relations = [F(relation.holonomy[::-1]) for relation in self.get_dual_relations()]
			# NEW ONE (MAKES MORE SENSE)
			relations = [F(relation.holonomy) for relation in self.get_dual_relations()]
			self.sage_dual_group = F / relations
		return self.sage_dual_group

	def dual_group_ring(self):
		if self.sage_dual_group_ring is None:
			self.sage_dual_group_ring = self.dual_fundamental_group().algebra(ZZ)
		return self.sage_dual_group_ring

	# Takes in a holonomy element and outputs an integer vector where the i-th entry is the
	# exponent of the i-th generator of the fundamental group after abelianizing the word
	def holonomy_exponents(self, hol):
		num_generators = len(self.face_orbits)
		vec = vector(ZZ, num_generators)
		for el in hol.holonomy:
			if el > 0:
				vec[abs(el) - 1] += 1
			elif el < 0:
				vec[abs(el) - 1] -= 1
			else:
				raise Exception('0 was a holonomy element')
		return vec

	def exponent_vec_to_abelianization(self, vec):
		gens = self.fundamental_group_abelianization().gens()
		assert len(gens) == len(vec)
		result = self.fundamental_group_abelianization().one()
		for i, el in enumerate(vec):
			result *= gens[i] ** el
		return result

	# Stolen from Snappy
	def map_to_dual_abelianization(self):
		ab_words = [self.holonomy_exponents(relation) for relation in self.get_dual_relations()]
		# R is the transpose of the presentation matrix of the abelianization
		# where we normally think of an element of the group as a row vector
		R = matrix(ZZ, ab_words).transpose()
		D, U, V = R.smith_form()
		m = U.nrows()
		assert m == D.nrows()
		d = min(D.nrows(), D.ncols())
		diag = D.diagonal()
		num_ones = diag.count(1)
		num_zeros = diag.count(0)
		rank = num_zeros + m - d
		U = U[num_ones:]
		generators = ['t%s' % i for i in range(len(diag[num_ones:-num_zeros]))] + ['f%s' % i for i in range(rank)]
		print(generators)
		self.abelianization = AbelianGroup(diag[num_ones:] + [0, ] * (m - d), names=generators)
		print(self.fundamental_group_abelianization().gens_orders())

		def ab(hol):
			return self.fundamental_group_abelianization()(U * self.holonomy_exponents(hol))

		# return self.exponent_vec_to_abelianization(U*self.holonomy_exponents(hol))
		return ab

	def fundamental_group_abelianization(self):
		if self.abelianization is None:
			self.map_to_dual_abelianization()
		return self.abelianization

	def map_to_dual_abelianization_ring(self):
		phi = self.map_to_dual_abelianization()
		if self.abelianization_ring is None:
			self.abelianization_ring = self.abelianization.algebra(ZZ)

		def phi2(hol):
			return self.abelianization_ring(phi(hol))

		return phi2

	def dual_abelianization_ring(self):
		if self.abelianization is None:
			self.map_to_dual_abelianization_ring()
		return self.abelianization_ring

	def map_to_dual_free_abelianization(self):
		ab_words = [self.holonomy_exponents(relation) for relation in self.get_dual_relations()]
		# R is the transpose of the presentation matrix of the abelianization
		# where we normally think of an element of the group as a row vector
		R = matrix(ZZ, ab_words).transpose()
		D, U, V = R.smith_form()
		m = U.nrows()
		assert m == D.nrows()
		d = min(D.nrows(), D.ncols())
		diag = D.diagonal()
		num_ones = diag.count(1)
		num_zeros = diag.count(0)
		num_torsion = len(diag)-num_ones-num_zeros
		rank = num_zeros + m - d
		U = U[num_ones+num_torsion:]
		self.free_abelianization = AbelianGroup(rank, names=['f%s' % i for i in range(rank)])
		# print(self.fundamental_group_abelianization().gens_orders())

		def ab(hol):
			if rank == 0:
				return self.free_fundamental_group_abelianization()(1)
			else:
				return self.free_fundamental_group_abelianization()((U * self.holonomy_exponents(hol)))

		# return self.exponent_vec_to_abelianization(U*self.holonomy_exponents(hol))
		return ab

	def free_fundamental_group_abelianization(self):
		if self.free_abelianization is None:
			self.map_to_dual_free_abelianization()
		return self.free_abelianization

	def map_to_free_abelianization_ring(self):
		phi = self.map_to_dual_free_abelianization()
		if self.free_abelianization_ring is None:
			if len(self.free_abelianization.gens()) == 0:
				self.free_abelianization_ring = self.free_abelianization.algebra(ZZ)
			else:
				self.free_abelianization_ring = LaurentPolynomialRing(ZZ, len(self.free_abelianization.gens()), 'z')

		def phi2(hol):
			gens = self.free_abelianization_ring.gens()
			exponents = phi(hol).exponents()
			result = self.free_abelianization_ring(1)
			for i, exp in enumerate(exponents):
				result = result*(gens[i]**exp)
			return result

		return phi2

	def dual_free_abelianization_ring(self):
		if self.free_abelianization is None:
			self.map_to_dual_free_abelianization_ring()
		return self.free_abelianization_ring
	# ---------------------------------Normal Homology----------------------------------

	# Calculate the (non-dual) first boundary map, with coefficients twisted by phi
	def B1(self):
		codomain_dimension = len(self.vertex_orbits)
		domain_dimension = len(self.edge_orbits)
		b = matrix(ZZ, codomain_dimension, domain_dimension)
		for j in range(domain_dimension):
			edge = self.edge_orbits[j]
			b[edge.head.index, j] += 1
			b[edge.tail.index, j] += -1
		return b

	def B2(self, rep=True):
		codomain_dimension = len(self.edge_orbits)
		domain_dimension = len(self.face_orbits)
		b = matrix(ZZ, codomain_dimension, domain_dimension)
		if rep:
			for j in range(domain_dimension):
				face = self.face_orbits[j].preferred
				for edge in face.edges:
					b[edge.orbit.index, j] += face.edge_sign(edge)
			return b
		else:
			for j in range(domain_dimension):
				face = self.face_orbits[j]
				for edge in face.edges:
					b[edge.index, j] += face.edge_sign(edge)
			return b

	def B3(self):
		codomain_dimension = len(self.face_orbits)
		domain_dimension = 1
		return matrix(ZZ, codomain_dimension, domain_dimension, entries=0)

	def homology_chain_complex(self):
		diffs = {1: self.B1(), 2: self.B2(), 3: self.B3()}
		C = ChainComplex(base_ring=ZZ, data=diffs, degree=-1, check=True)
		return C

	# -------------------------------Twisted (and Dual) Homology---------------------------

	# Checks to make sure that the given representation is actually a representation
	# i.e. that when applied on the fundamental group relations, it gives the identity.
	def check_representation(self, phi, tol=.0001):
		for relation in self.get_dual_relations():
			if not equal_matrices(phi(relation), 1, tol):
				print((phi(relation) - 1).norm('frob'))
				raise Exception('Representation is not good within given tolerance')
		return True

	# DO NOT NEED TO DO ANYTHING SPECIAL WITH OUTPUT
	# Applies involution
	def fox_deriv(self, holonomy, num, phi):
		if len(holonomy.holonomy) == 1:
			letter = holonomy.holonomy[0]
			if abs(letter) == num:
				if letter < 0:
					return -phi(holonomy.inverse())
				else:
					return 1
			else:
				return 0
		else:
			return self.fox_deriv(holonomy[0], num, phi) + self.fox_deriv(holonomy[1:], num, phi) * phi(
				holonomy[0].inverse())

	@staticmethod
	def _setup_boundaries(phi=None, ring=ZZ, dimension=1, identity=None, as_list=False):
		if identity is None:
			if dimension == 1:
				identity = ring(1)
			else:
				identity = matrix.identity(ring, dimension)
		if phi is None:
			phi = lambda x: identity
		return phi, ring, dimension, identity, as_list

	# Calculates the boundary map C_1 -> C_0 of the twisted chain complex of the dual cellulation
	# phi is a homomorphism which takes HolonomyElement and returns an element of GL(dimension,ring).
	def dualB1(self, **args):
		phi, ring, dimension, identity, as_list = self._setup_boundaries(**args)
		codomain_dimension = 1
		domain_dimension = len(self.holonomy_generators)
		b = []
		for j in range(domain_dimension):
			# face = self.face_orbits[j]
			# Inverse is applying the involution
			phi_of_hol = phi(self.holonomy_generators[j].inverse())
			# ~ print(phi_of_hol.parent())
			# ~ print(identity.parent())
			b.append(phi_of_hol - 1)
		if as_list:
			return b
		if dimension == 1:
			return matrix(ring, codomain_dimension, domain_dimension, b)
		else:
			# IS TAKING THE TRANSPOSE OKAY??
			return matrix.block(ring, codomain_dimension, domain_dimension, [a for a in b], subdivide=dimension != 1)

	# Calculates the boundary map C_2 -> C_1 of the twisted chain complex of the dual cellulation
	# phi is a homomorphism which takes HolonomyElement and returns an element of GL(dimension,ring).
	def dualB2(self, **args):
		phi, ring, dimension, identity, as_list = self._setup_boundaries(**args)
		codomain_dimension = len(self.face_orbits)
		domain_dimension = len(self.edge_orbits)
		b = []
		for i in range(codomain_dimension):
			for relation in self.get_dual_relations():
				b.append(self.fox_deriv(relation, i + 1, phi))
		# ~ print('before printing b')
		# ~ for el in b:
		# ~ print(b)
		# ~ #print(b)
		# ~ print('after printing b')
		if as_list:
			return b
		if dimension == 1:
			return matrix(ring, codomain_dimension, domain_dimension, b)
		else:
			# IS TAKING THE TRANSPOSE OKAY??
			return matrix.block(ring, codomain_dimension, domain_dimension, [a for a in b], subdivide=dimension != 1)

	# Calculates the boundary map C_3 -> C_2 of the twisted chain complex of the dual cellulation
	# phi is a homomorphism which takes HolonomyElement and returns an element of GL(dimension,ring).
	def dualB3(self, **args):
		phi, ring, dimension, identity, as_list = self._setup_boundaries(**args)
		zero = identity - identity
		domain_dimension = len(self.vertex_orbits)
		codomain_dimension = len(self.edge_orbits)
		b = []
		for j in range(domain_dimension):
			vertex_orbit = self.vertex_orbits[j]
			b_j = [zero] * codomain_dimension
			for edge_orbit in vertex_orbit.adjacent_edges:
				if edge_orbit.head == vertex_orbit:
					lift = edge_orbit.lift(vertex_orbit.preferred, head=True)
					b_j[edge_orbit.index] -= phi(lift.holonomy.inverse())
					assert lift.head.holonomy == vertex_orbit.preferred.holonomy
					assert lift.head.orbit == vertex_orbit
				if edge_orbit.tail == vertex_orbit:
					lift = edge_orbit.lift(vertex_orbit.preferred, tail=True)
					b_j[edge_orbit.index] += phi(lift.holonomy.inverse())
					assert lift.tail.holonomy == vertex_orbit.preferred.holonomy
					assert lift.tail.orbit == vertex_orbit
			b.append(b_j)
		if as_list:
			return b
		if dimension == 1:
			return matrix(ring, domain_dimension, codomain_dimension, b).transpose()
		else:
			# IS TAKING THE TRANSPOSE OKAY??
			return matrix.block(ring, domain_dimension, codomain_dimension, [a.transpose() for c in b for a in c],
								subdivide=dimension != 1).transpose()

	# phi is a homomorphism which takes HolonomyElement and returns an element of GL(dimension,ring).
	def reduced_dualB2(self, **args):
		phi, ring, dimension, identity, as_list = self._setup_boundaries(**args)
		codomain_dimension = len(self.face_orbits)
		domain_dimension = len(self.essential_edge_orbits)
		b = []
		for i in range(codomain_dimension):
			for relation in self.get_dual_relations(reduced=True):
				b.append(self.fox_deriv(relation, i + 1, phi))
		if as_list:
			return b
		if dimension == 1:
			return matrix(ring, codomain_dimension, domain_dimension, b)
		else:
			# IS TAKING THE TRANSPOSE OKAY??
			return matrix.block(ring, codomain_dimension, domain_dimension, [a for a in b], subdivide=dimension != 1)

	# phi is a homomorphism which takes HolonomyElement and returns an element of GL(dimension,ring).
	def reduced_dualB3(self, **args):
		phi, ring, dimension, identity, as_list = self._setup_boundaries(**args)
		domain_dimension = 1
		codomain_dimension = len(self.essential_edge_orbits)
		# print('codomain_dimension {0}'.format(codomain_dimension))
		b = []
		for edge_orbit in self.essential_edge_orbits:
			# head_orbit = edge_orbit.head
			# option 1
			# edge_lift = edge_orbit.lift(head_orbit.preferred, head = True)
			# b.append(identity - phi(edge_lift.tail.holonomy.inverse())

			# option 2
			# ~ orbit_path = self.shortest_path_in_orbit_tree(head_orbit, edge_orbit.tail)
			# ~ path_lift = self.path_lift(orbit_path,head_orbit.preferred, report_vertices = True)
			# ~ end_vertex = path_lift[-1]
			# ~ edge_lift = edge_orbit.lift(end_vertex, tail = True)
			# ~ other_head = edge_lift.head
			# ~ assert head_orbit.preferred.orbit == other_head.orbit
			# ~ b.append(identity - phi(other_head.holonomy.inverse()))

			orbits = [edge_orbit.head, edge_orbit.tail]
			hols = []
			for i, orbit in enumerate(orbits):
				if self.vertex_orbits[0] == orbit:
					end_vertex = self.vertex_orbits[0].preferred
				else:
					orbit_path = self.shortest_path_in_orbit_tree(self.vertex_orbits[0], orbit)
					path_lift = self.path_lift(orbit_path, self.vertex_orbits[0].preferred, report_vertices=True)
					end_vertex = path_lift[-1]
				if i == 0:
					lift = edge_orbit.lift(end_vertex, head=True)
				else:
					# print(end_vertex)
					lift = edge_orbit.lift(end_vertex, tail=True)
				# decking the hols
				hols.append(phi(lift.holonomy.inverse()))
			if isinstance((hols[1]-hols[0]), int):
				print(hols)
				print(phi(hols[0]), phi(hols[1]))
				raise(Exception('got int instead of matrix'))
			b.append(hols[1] - hols[0])
		if as_list:
			return b
		if dimension == 1:
			return matrix(ring, codomain_dimension, domain_dimension, b)
		else:
			return matrix.block(ring, codomain_dimension, domain_dimension,
								[a.transpose().transpose() for a in b], subdivide=True)

	# Doesn't support non-SL(2,C) representations yet
	def torsion_polynomial(self, phi=None, time_determinant=False):
		if phi is None:
			if self.moebius_transformations is None:
				raise Exception('No Moebius transformations available to construct the torsion polynomial')
			else:
				phi = phi_from_face_mapping(self.moebius_transformations)
		alpha = self.map_to_free_abelianization_ring()
		CCHP = ComplexField(self.precision)
		ring = LaurentPolynomialRing(CCHP, len(self.free_abelianization.gens()), 'z')
		free_ab = self.free_abelianization_ring
		assert is_nonprojective_representation(self.moebius_transformations, self.get_dual_relations())
		assert self.check_representation(phi)

		def phi_alpha(holonomy):
			mat = phi(holonomy)
			mat = matrix(ring, mat)
			return alpha(holonomy)*mat

		b1 = self.dualB1(phi=phi_alpha, ring=ring, dimension=2)
		b2 = self.reduced_dualB2(phi=phi_alpha, ring=ring, dimension=2)
		b3 = self.reduced_dualB3(phi=phi_alpha, ring=ring, dimension=2)

		# print(b2*b3)
		# print(b1*b2)
		# assert is_essentially_zero((b2*b3).substitute(z=.01)) and is_essentially_zero((b1*b2).substitute(z=.01))
		ab_b1 = self.dualB1(phi=alpha, ring=free_ab)
		ab_b3 = self.reduced_dualB3(phi=alpha, ring=free_ab)
		# print(ab_b1)
		# print(ab_b3)
		one_index = [i for i in range(ab_b1.ncols()) if ab_b1[0, i] != free_ab(0)][0]
		three_index = [i for i in range(ab_b3.nrows()) if ab_b3[i, 0] != free_ab(0)][0]

		n = b2.nrows()

		# The matrix tau-chain (for more, see Introduction to Combinatorial Torsion by Turaev)
		# a_0 = []
		a_1 = [2*one_index, 2*one_index+1]
		a_2 = [el for el in range(n) if el not in [three_index * 2, three_index * 2 + 1]]
		a_3 = [0, 1]
		# print('a_2')
		# print(a_2)
		# The complement of the matrix tau chain (to calculate the rows)
		a_0c = [0, 1]
		a_1c = [el for el in range(n) if el not in a_1]
		a_2c = [el for el in range(n) if el not in a_2]
		# a_3c = []
		S_0 = b1.matrix_from_columns(a_1)
		S_1 = b2.matrix_from_columns(a_2)
		assert b3.matrix_from_columns(a_3) == b3

		# print(S_1)
		assert S_0.matrix_from_rows(a_0c) == S_0
		S_1 = S_1.matrix_from_rows(a_1c)
		S_2 = b3.matrix_from_rows(a_2c)

		matches = [-CCHP(1), CCHP(0), CCHP(1), CCHP(2), CCHP(-2), CCHP.gen(), -CCHP.gen()]

		def clean_coefficient(coeff):
			for num in matches:
				if (coeff - num).abs() < 10 ** (-12):
					return num
			return coeff
		# print(S_1)

		old_S1 = S_1
		S_0 = poly.laurent_matrix_to_poly_matrix(S_0)
		S_1 = poly.laurent_matrix_to_poly_matrix(S_1)
		S_2 = poly.laurent_matrix_to_poly_matrix(S_2)
		debugging = True
		if debugging:
			return old_S1, S_1
		S_0 = poly.clean_polynomial_matrix(S_0)
		S_1 = poly.clean_polynomial_matrix(S_1)
		S_2 = poly.clean_polynomial_matrix(S_2)

		if S_1.base_ring().ngens() == 1:
			S_1 = S_1.change_ring(PolynomialRing(CCHP, S_1.base_ring().gen()))
			tic = time.perf_counter()
			numerator = S_1.determinant()
			if time_determinant:
				toc = time.perf_counter()
				print('It took %s seconds to calculate the determinant of the big matrix' % (toc - tic))
			numerator = poly.clean_polynomial(numerator)
			numerator = poly.factor_out_monomial(numerator)[0]
			denominator = S_0.determinant() * S_2.determinant()
			denominator = poly.clean_polynomial(denominator)
			denominator = poly.factor_out_monomial(denominator)[0]
			quorem = numerator.quo_rem(denominator())
			rem = quorem[1]
			quotient = quorem[0]
			rem_coeffs = rem.coefficients()
			coeff_mags = [coeff.abs() for coeff in rem_coeffs]
			max_coeff = max(coeff_mags)
			if max_coeff > 10**(-8):
				print('numerator did not divide denominator. max coefficient was {0}'.format(max_coeff))
				return numerator, denominator
			else:
				quotient = quotient.map_coefficients(clean_coefficient)
				return poly.factor_out_monomial(quotient)[0]
		else:
			if time_determinant:
				print('starting to take determinant')
			tic = time.perf_counter()
			numerator = S_1.determinant()
			if time_determinant:
				toc = time.perf_counter()
				print('It took %s seconds to calculate the determinant of the big matrix' % (toc - tic))
			numerator = numerator.map_coefficients(clean_coefficient)
			denominator = S_0.determinant() * S_2.determinant()
			denominator = denominator.map_coefficients(clean_coefficient)
			denominator = poly.laurent_to_poly(denominator)
			numerator = poly.factor_out_monomial(numerator)[0]
			print('numerator:\n{0}\ndenominator:\n{1}'.format(numerator, denominator))
			quorem = numerator.quo_rem(denominator)
			# quorem = poly.quo_rem(numerator, denominator)
			rem = quorem[1]
			quotient = quorem[0]
			rem_coeffs = rem.coefficients()
			coeff_mags = [coeff.abs() for coeff in rem_coeffs]
			max_coeff = max(coeff_mags)
			if max_coeff > 10 ** (-8):
				print('numerator did not divide denominator. max coefficient was {0}'.format(max_coeff))
				return numerator, denominator
			else:
				quotient = quotient.map_coefficients(clean_coefficient)
				return quotient

# For matrices over exact fields
	def exact_torsion_polynomial(self, phi, base_ring, dimension=2, time_determinant=False):
		if phi is None:
			raise Exception('No Moebius transformations available to construct the torsion polynomial')
		alpha = self.map_to_free_abelianization_ring()
		lring = LaurentPolynomialRing(base_ring, len(self.free_abelianization.gens()), 'z')
		free_ab = self.free_abelianization_ring

		def phi_alpha(holonomy):
			mat = phi(holonomy)
			mat = matrix(lring, mat)
			return alpha(holonomy)*mat

		b1 = self.dualB1(phi=phi_alpha, ring=lring, dimension=dimension)
		b2 = self.reduced_dualB2(phi=phi_alpha, ring=lring, dimension=dimension)
		b3 = self.reduced_dualB3(phi=phi_alpha, ring=lring, dimension=dimension)

		# print(b2*b3)
		# print(b1*b2)
		# assert is_essentially_zero((b2*b3).substitute(z=.01)) and is_essentially_zero((b1*b2).substitute(z=.01))
		ab_b1 = self.dualB1(phi=alpha, ring=free_ab)
		ab_b3 = self.reduced_dualB3(phi=alpha, ring=free_ab)
		# print(ab_b1)
		# print(ab_b3)
		one_index = [i for i in range(ab_b1.ncols()) if ab_b1[0, i] != free_ab(0)][0]
		three_index = [i for i in range(ab_b3.nrows()) if ab_b3[i, 0] != free_ab(0)][0]

		n = b2.nrows()

		# The matrix tau-chain (for more, see Introduction to Combinatorial Torsion by Turaev)
		# a_0 = []
		a_1 = [dimension*one_index+i for i in range(dimension)]
		a_2 = [el for el in range(n) if el not in [dimension*three_index + i for i in range(dimension)]]
		a_3 = [0, 1]
		# print('a_2')
		# print(a_2)
		# The complement of the matrix tau chain (to calculate the rows)
		a_0c = [0, 1]
		a_1c = [el for el in range(n) if el not in a_1]
		a_2c = [el for el in range(n) if el not in a_2]
		# a_3c = []
		S_0 = b1.matrix_from_columns(a_1)
		S_1 = b2.matrix_from_columns(a_2)
		assert b3.matrix_from_columns(a_3) == b3

		# print(S_1)
		assert S_0.matrix_from_rows(a_0c) == S_0
		S_1 = S_1.matrix_from_rows(a_1c)
		S_2 = b3.matrix_from_rows(a_2c)
		if time_determinant:
			print('starting to take determinant')
		tic = time.perf_counter()
		numerator = poly.laurent_to_poly(S_1.determinant())
		if time_determinant:
			toc = time.perf_counter()
			print('It took %s seconds to calculate the determinant of the big matrix' % (toc - tic))
		denominator = poly.laurent_to_poly(S_0.determinant() * S_2.determinant())
		# numerator = poly.factor_out_monomial(numerator)[0]
		# denominator = poly.factor_out_monomial(denominator)[0]
		# print('numerator:\n{0}\ndenominator:\n{1}'.format(numerator, denominator))
		quorem = numerator.quo_rem(denominator)
		# quorem = poly.quo_rem(numerator, denominator)
		rem = quorem[1]
		quotient = quorem[0]
		if rem.degree() >= 0:
			print('numerator did not divide denominator. remainder was {0}'.format(rem))
			return numerator, denominator
		else:
			return poly.factor_out_monomial(quotient)[0]


# ----------------------------------Holonomy----------------------------------
# THIS WHAT MAKES IT OP
# Throughout this program, we are using the convention that (cell)[a,b,c]=c(b(a(cell)))
class HolonomyElement(object):
	def __init__(self, tietze=None, face_list=None, domain=None):
		if face_list is not None:
			self.holonomy = self.Tietze(face_list)
		if tietze is not None:
			self.holonomy = tietze
		while self.reduce():
			pass
		self.domain = domain

	def __str__(self):
		return 'Hol{0}'.format(self.holonomy)

	@staticmethod
	def Tietze(faces):
		return [int((-1) ** (i % 2) * ((i - i % 2) / 2 + 1)) for i in faces]

	def as_face_list(self):
		sign = lambda x: 0 if x > 0 else 1
		return [2 * (abs(i) - 1) + sign(i) for i in self.holonomy]

	def apply(self, cell, suppress=False):
		if cell is None:
			return None
		elif isinstance(cell, Vertex):
			return self.apply_on_vertex(cell)
		elif isinstance(cell, Edge):
			return self.apply_on_edge(cell)
		elif isinstance(cell, Face):
			return self.apply_on_face(cell)
		else:
			if not suppress:
				print('applying holonomy on unknown cell type')
			return self.compose(cell.holonomy)

	# returns false if it could not be reduced, true otherwise
	def reduce(self):
		for i, hol in enumerate(self.holonomy):
			if i == len(self.holonomy) - 1:
				return False
			if hol == -self.holonomy[i + 1]:
				self.holonomy = self.holonomy[:i] + self.holonomy[i + 2:]
				return True

	def reduceable(self):
		for i, hol in enumerate(self.holonomy):
			if i == len(self.holonomy) - 1:
				return False
			elif hol == -self.holonomy[i + 1]:
				return True

	# composes this holonomy element on the left of the given and returns the result
	def compose(self, hol):
		return HolonomyElement(self.holonomy + hol.holonomy, domain=self.domain)

	def inverse(self):
		return HolonomyElement([-i for i in self.holonomy[::-1]], domain=self.domain)

	def apply_on_vertex(self, vertex):
		return Vertex(vertex.orbit, self.compose(vertex.holonomy))

	def apply_on_edge(self, edge):
		return Edge(edge.orbit, self.compose(edge.holonomy), self.apply(edge.tail), self.apply(edge.head))

	def apply_on_face(self, face):
		new_vertices = [self.apply(cell) for cell in face.vertices]
		new_edges = [self.apply(cell) for cell in face.edges]
		new_vertex_images = [self.apply(cell) for cell in face.paired_vertices]
		new_edge_images = [self.apply(cell) for cell in face.paired_edges]
		return Face(face.orbit, self.compose(face.holonomy), new_vertices, new_edges, new_vertex_images,
					new_edge_images)

	def matrix(self):
		if self.domain.pairing_matrices is None:
			raise Exception('No representation available')
		else:
			out = matrix.identity(4, RR)
			for i in self.holonomy:
				sign = 1 if i < 0 else 0
				i = 2 * (abs(i)-1) + sign
				out = out*self.domain.pairing_matrices[i]
			return out

	def __getitem__(self, key):
		if isinstance(key, tuple):
			if len(key) > 1:
				raise IndexError('HolonomyElement does not support multiple indexing')
			else:
				key = key[0]
		elif isinstance(key, slice):
			return HolonomyElement(self.holonomy[key], domain=self.domain)
		return HolonomyElement([self.holonomy[key]], domain=self.domain)

	def __eq__(self, other):
		if not isinstance(other, HolonomyElement):
			print('goes here')
			return False
		else:
			return self.holonomy == other.holonomy

	def __hash__(self):
		return sum([(2**i)*self.holonomy[i] for i in range(len(self.holonomy))])*hash(self.domain)


# -----------------------------GENERAL USE-----------------------------------------
def fox_deriv(holonomy, num, phi):
	if len(holonomy.holonomy) == 1:
		letter = holonomy.holonomy[0]
		if abs(letter) == num:
			if letter < 0:
				return -phi(holonomy.inverse())
			else:
				return 1
		else:
			return 0
	else:
		return fox_deriv(holonomy[0], num, phi) + fox_deriv(holonomy[1:], num, phi) * phi(holonomy[0].inverse())


# -----------------------------Testing-------------------------------
def find_face(nathan_d, vertices):
	for face in nathan_d.faces:
		if set(vertices) == set(face.indices):
			return face
	raise(Exception('face not found'))


# WARNING: d_domain.py will usually throw a bunch of errors due to imprecision in this test
# To fix, comment out the following line in d_domain
# assert mp.mnorm(point - match) < 5000*mp.eps, ('Point match', mp.mnorm(point - match), 5000*mp.eps)
# to stop these errors


# WARNING: d_domain.py will usually throw a bunch of errors due to imprecision in this test
# To fix, comment out the following line in d_domain
# assert mp.mnorm(point - match) < 5000*mp.eps, ('Point match', mp.mnorm(point - match), 5000*mp.eps)
# to stop these errors


# DD.orbit_digraph.plot(edge_labels=True).save('./pictures' + string + '_orbit_digraph.png')
	# DD.orbit_graph.plot(edge_labels=True).save('./pictures' + string + '_orbit_graph.png')
	# DD.digraph.plot(edge_labels=True).save('./pictures' + string + '_digraph.png')
	# DD.graph.plot(edge_labels=True).save('./pictures' + string + '_graph.png')


# tests the twisted boundary maps, using the O(3,1) representation of the fundamental group from snappy
# print('d2\n\n\n')
	# print(DD.dualB2(phi=phi, ring=RR, dimension=4).n(digits=3))
	# print('d3\n\n\n')
	# print(DD.dualB3(phi=phi, ring=RR, dimension=4).n(digits=3))


# print('d2\n\n\n')
# print(DD.dualB2(phi=phi, ring=RR, dimension=4).n(digits=3))
# print('d3\n\n\n')
# print(DD.dualB3(phi=phi, ring=RR, dimension=4).n(digits=3))


# Tests on the genus 2 surface with the presentation <a,b,c,d|aBAbcDCd>


# ~ print(DD.dual_fundamental_group().abelian_invariants())
# ~ print('EDGES')
# ~ for i in range(len(DD.edges)):
# ~ edge=DD.edges[i]
# ~ print(edge.tail.index,edge.head.index)
# ~ #print([str(edge) for edge in DD.edges])
# ~ print('FACES')
# ~ for i in range(len(DD.face_list)):
# ~ face = DD.face_list[i]
# ~ print([x.index for x in face.edges],[x.index for x in face.paired_edges])
# ~ print([str(face) for face in DD.face_list])
# ~ save_graphs(D,'SW')
# ~ print('Me reduced dual B2 \n{0}'.format(DD.reduced_dualB2()))
# ~ print('Me reduced dual B2 smith form\n{0}'.format(DD.reduced_dualB2().smith_form()[0]))
# ~ print('Me reduced dual B3 \n{0}'.format(DD.reduced_dualB3()))
# ~ print('Me reduced_dual B3 smith fom \n{0}'.format(DD.reduced_dualB3().smith_form()[0]))
# ~ print('Me reduced dual B2*B3 \n{0}'.format(DD.reduced_dualB2()*DD.reduced_dualB3()))
# ~ print('Me reduced dual B1*B2 \n{0}'.format(DD.dualB1()*DD.reduced_dualB2()))


# ~ print(DD.dual_fundamental_group().abelian_invariants())
# ~ print('EDGES')
# ~ for i in range(len(DD.edges)):
# ~ edge=DD.edges[i]
# ~ print(edge.tail.index,edge.head.index)
# ~ #print([str(edge) for edge in DD.edges])
# ~ print('FACES')
# ~ for i in range(len(DD.face_list)):
# ~ face = DD.face_list[i]
# ~ print([x.index for x in face.edges],[x.index for x in face.paired_edges])
# ~ print([str(face) for face in DD.face_list])
# ~ save_graphs(D,'SW')
# ~ print('Me reduced dual B2 \n{0}'.format(DD.reduced_dualB2()))
# ~ print('Me reduced dual B2 smith form\n{0}'.format(DD.reduced_dualB2().smith_form()[0]))
# ~ print('Me reduced dual B3 \n{0}'.format(DD.reduced_dualB3()))
# ~ print('Me reduced_dual B3 smith fom \n{0}'.format(DD.reduced_dualB3().smith_form()[0]))
# ~ print('Me reduced dual B2*B3 \n{0}'.format(DD.reduced_dualB2()*DD.reduced_dualB3()))
# ~ print('Me reduced dual B1*B2 \n{0}'.format(DD.dualB1()*DD.reduced_dualB2()))




# FIGURE OUT ORIENTATIONS AND SPECIFICS OF DUAL CELLS

# sage -pip install --upgrade git+https://github.com/3-Manifolds/SnapPy



# Lin and Lipnowski paper
# https://arxiv.org/pdf/2003.11165.pdf
