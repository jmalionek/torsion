import math

from sage.all import RR, vector, Combinations, ZZ, matrix, floor

Alphabet = '$abcdefghijklmnopqrstuvwxyzZYXWVUTSRQPONMLKJIHGFEDCBA'


# Takes in a twistable domain object and determines whether edges can be removed from the dirichlet domain.
def simplifiable(tdomain):
	removable = []
	faces_by_edge = {}
	for face in tdomain.face_list:
		for edge in face.edges:
			if edge in faces_by_edge.keys():
				faces_by_edge[edge] = [faces_by_edge[edge], face]
			else:
				faces_by_edge[edge] = face
	for edge in tdomain.edges:
		face1, face2 = faces_by_edge[edge]
		if face1.opposite_edge(edge) == face2.opposite_edge(edge):
			removable.append(edge)
	return removable


class AbstractVertex(object):
	def __init__(self):
		self.adjacent_edges = []

	def __str__(self):
		return 'v{0}'.format(self.index)


class AbstractEdge(object):
	def __init__(self, tail, head):
		self.head = head
		self.tail = tail
		self.adjacent_faces = []

	def endpoints(self):
		return [self.tail, self.head]

	def other_endpoint(self, vertex):
		if vertex == self.head:
			return self.tail
		elif vertex == self.tail:
			return self.head
		else:
			raise Exception('Given vertex is not an endpoint of this cell')

	def __str__(self):
		return 'e{0}'.format(self.index)


class AbstractFace(object):
	def __init__(self, vertices=None, edges=None, edge_orientations=None):
		self.vertices = vertices
		self.edges = edges
		self.edge_orientations = edge_orientations

	def edge_sign(self, edge):
		index = self.edges.index(edge)
		return self.edge_orientations[index]

	def __str__(self):
		return 'f{0}'.format(self.index)


class AbstractPolyhedron(object):
	def __init__(self, faces=None):
		self.faces = faces


class Cell(object):
	def __init__(self, orbit=None, holonomy=None, index=None):
		self.index = index
		self.orbit = orbit
		self.holonomy = holonomy


class CellClass(object):
	def __init__(self, preferred=None, index=None, cells=None):
		if cells is None:
			cells = []
		self.index = index
		self.cells = cells
		self.preferred = preferred

	def add(self, cell):
		self.cells.append(cell)
		cell.orbit = self

	def get_reps(self):
		return self.cells

	def get_rep_indices(self):
		return [cell.index() for cell in self.cells]

	def __str__(self):
		return str(self.cells)


class Vertex(Cell, AbstractVertex):
	def __init__(self, orbit=None, holonomy=None, index=None, coords=None):
		Cell.__init__(self, orbit, holonomy, index)
		AbstractVertex.__init__(self)
		if coords is not None:
			self.set_coords(coords)
		else:
			self.coords = None

	def __str__(self):
		return '{0}(V{1})'.format(self.holonomy.holonomy, str(self.orbit.index))

	def __hash__(self):
		if self.index is None:
			return hash(self.holonomy)
		else:
			return hash(self.holonomy)*self.index

	def set_coords(self, coords):
		self.coords = vector([1, 0, 0, 0], RR)
		for i in range(3):
			self.coords[i+1] = float(coords[i])
		self.coords = self.coords / math.sqrt(abs(1 - sum(self.coords[i] ** 2 for i in range(1, 4))))

	# Returns the coordinates obtained by applying the holonomy on the coordinates of the preferred vertex
	def coords_from_holonomy(self):
		return self.holonomy.matrix()*self.orbit.preferred.coords


class VertexOrbit(CellClass, AbstractVertex):
	def __init__(self, preferred=None, index=None, cells=None):
		CellClass.__init__(self, preferred, index, cells)
		AbstractVertex.__init__(self)

	def __str__(self):
		return 'V{0}'.format(self.index)


class Edge(AbstractEdge, Cell):
	def __init__(self, orbit=None, holonomy=None, tail=None, head=None, index=None):
		Cell.__init__(self, orbit, holonomy, index)
		AbstractEdge.__init__(self, tail, head)

	def __str__(self):
		return '{0}(E{1})'.format(self.holonomy.holonomy, str(self.orbit.index))

	def __hash__(self):
		return hash(self.head) * hash(self.tail) * hash(self.holonomy)


class EdgeOrbit(CellClass, AbstractEdge):
	def __init__(self, preferred=None, tail=None, head=None, index=None):
		CellClass.__init__(self, preferred, index)
		AbstractEdge.__init__(self, tail, head)

	# Returns the lift of this edge which starts at the given vertex.
	# if head or tail is True (if both are true, this will throw an error)
	# this will check to make sure that the given lift will have its head or tail at the
	# specified vertex.
	# If neither is specified, this will make sure that one of them is
	# (and will print a warning if both are of them are, as the lift will not be unique
	# in this case, it will give the lift from the tail)
	def lift(self, vertex, head=None, tail=None):
		assert not (head and tail)
		if head is None and tail is None:
			assert vertex.orbit in [self.head, self.tail]
			if vertex.orbit == self.head and vertex.orbit == self.tail:
				print(
					'Warning: Given edge is a loop and head or tail not specified. Lift will not be unique, '
					'tail is chosen')
				tail = True
			if vertex.orbit == self.head:
				head = True
			elif vertex.orbit == self.tail:
				tail = True
		edge = self.preferred
		if tail:
			assert self.tail == vertex.orbit
			to_initial = edge.tail.holonomy.inverse()
		elif head:
			assert self.head == vertex.orbit
			to_initial = edge.head.holonomy.inverse()
		else:
			raise Exception('Should not have reached here')
		edge = to_initial.apply(edge)
		return vertex.holonomy.apply(edge)

	def __str__(self):
		return 'E{0}'.format(self.index)


class Face(Cell, AbstractFace):
	def __init__(self, orbit=None, holonomy=None, vertices=None, edges=None, paired_vertices=None, paired_edges=None,
				edge_orientations=None, index=None, paired_face=None):
		Cell.__init__(self, orbit, holonomy, index)
		AbstractFace.__init__(self, vertices, edges, edge_orientations)
		self.paired_vertices = paired_vertices
		self.paired_edges = paired_edges
		self.paired_face = paired_face

	def opposite_face(self):
		return self.paired_face

	def opposite_vertex(self, vertex):
		index = self.vertices.index(vertex)
		return self.paired_vertices[index]

	def opposite_edge(self, edge):
		index = self.edges.index(edge)
		return self.paired_edges[index]

	def get_Tietze(self):
		sign = -1 if self.index % 2 == 1 else 1
		return math.floor(self.index / 2) * sign

	def get_letter(self):
		if abs(self.index) > 26:
			raise Exception('Face index too high to get letter')
		return Alphabet[self.get_Tietze()]


class FaceOrbit(CellClass, AbstractFace):
	def __init__(self, preferred=None, vertices=None, edges=None, signs=None, index=None):
		CellClass.__init__(self, preferred, index)
		AbstractFace.__init__(self, vertices, edges, signs)


class Simplex:
	"""
	A class which represents a simplex in a triangulation of a manifold.
	In this case, we define a simplex by its faces as opposed to vertices so that the triangulation can represent delta
	complexes as opposed to pure simplicial complexes.
	"""
	def __init__(self, index, faces, face_orientations, data=None):
		self.index = index
		self.faces = faces
		self.dim = len(faces) - 1
		self.face_orientations = face_orientations
		self.data = data

	def dimension(self):
		return self.dim

	def boundary(self, n=None):
		"""
		Returns a list of all of the n-dimensional cells which are faces of this one. If n is None, this returns the
		boundary faces of this simplex
		"""
		assert self.dim >= n
		if n is None:
			n = self.dim - 1
		if n == self.dim:
			return {self}
		if n == self.dim - 1:
			return self.faces
		return set().union(*[face.boundary(n) for face in self.faces])

	def is_zero_simplex(self):
		return False

	def __hash__(self):
		return self.dimension()**self.index

	def __str__(self):
		return "(" + ','.join([str(face) for face in self.faces]) + ")"


class ZeroSimplex(Simplex):
	def __init__(self, index, coords=None, data=None):
		Simplex.__init__(self, index, faces=[], face_orientations=[], data=data)
		self.coords = coords

	def is_zero_simplex(self):
		return True

	def __hash__(self):
		return self.index

	def __str__(self):
		return "v_"+str(self.index)


class Triangulation:
	"""
	A class for organizing simplices in a triangulation. (Note that this is not a simplicial complex because two
	different simplices may have the same vertices)
	"""

	def __init__(self, vertices=None):
		self.simplices = dict()
		if vertices is not None:
			if isinstance(vertices, int):
				self.simplices[0] = [ZeroSimplex(i) for i in range(vertices)]
			elif isinstance(vertices, list):
				self.simplices[0] = [ZeroSimplex(i, coords) for i, coords in enumerate(vertices)]
		else:
			self.simplices[0] = []

	def get_dimension(self):
		return max(self.simplices.keys())


	def add_new_vertices(self, num, data=None):
		"""
		Adds num new vertices to this triangulation and returns them to the user
		"""
		if data is None:
			data = [None]*num
		new_vertices = [ZeroSimplex(len(self.simplices[0]) + i, data[i]) for i in range(num)]
		self.simplices[0].extend(new_vertices)
		return new_vertices

	def add_new_vertex(self, data=None):
		return self.add_new_vertices(1, [data])

	def add_new_simplex(self, faces, orientations, data=None):
		dim = len(faces) - 1
		if dim not in self.simplices.keys():
			self.simplices[dim] = []
		for face in faces:
			assert face in self.simplices[dim-1]
		assert len(faces) == len(orientations)
		new_simplex = Simplex(len(self.simplices[dim]), faces, orientations, data)
		self.simplices[dim].append(new_simplex)
		return new_simplex

	def add_new_simplices(self, faces_list, orientations_list, data=None):
		if data is None:
			data = [None]*len(faces_list)
		new_simplices = []

		for faces, orientations, datum in zip(faces_list, orientations_list, data):
			new_simplices.append(self.add_new_simplex(faces, orientations, datum))
		return new_simplices

	def get_boundary_map(self, n):
		"""
			Returns the boundary map of this delta complex going from C_{n} to C_{n-1}.
		"""
		C_n_size = len(self.simplices[n])
		C_n_minus1_size = len(self.simplices[n-1])
		# if C_n_size or C_nplus1_size
		boundary_matrix = matrix(ZZ, C_n_minus1_size, C_n_size)
		# print(C_n_size, C_n_minus1_size)
		# print(boundary_matrix)
		for simplex in self.simplices[n]:
			# print(simplex.face_orientations)
			for face, orientation in zip(simplex.faces, simplex.face_orientations):
				boundary_matrix[face.index, simplex.index] += orientation
		return boundary_matrix

	def subdivide(self, randomize_split=False, get_chain_maps=False):
		"""
		Given a 3-dimensional triangulation, subdivides by splitting each tetrahedron into 4 tetrahedra
		and a central octahedron and then splitting that central octahedron into 4 tetrahedra.
		If randomize_split is true, it will randomly choose an axis of the octahedron to split along.
		Otherwise, this subdivision algorithm is deterministic.

		Assumptions:
		1. The triangle faces are ordered in a loop.
		2. All the triangles have three distinct edges (but not necessarily three distinct vertices)
		"""
		assert self.get_dimension() <= 3
		triangulation = Triangulation()
		old_vertices = triangulation.add_new_vertices(len(self.simplices[0]))
		new_vertices = triangulation.add_new_vertices(len(self.simplices[1]))
		edge_front_halves = triangulation.add_new_simplices([[new_vertices[edge.index], old_vertices[edge.faces[1].index]]
															for edge in self.simplices[1]],
															[[-1, 1]]*len(self.simplices[1]))
		edge_back_halves = triangulation.add_new_simplices([[old_vertices[edge.faces[0].index], new_vertices[edge.index]]
															for edge in self.simplices[1]],
															[[-1, 1]] * len(self.simplices[1]))

		# For every edge of each triangle, there is an edge added on the face which is parallel to it
		# Organized as a list where each entry (corresponding to a triangle in the triangulation) is a list of three edges.
		# The edges are ordered with the same ordering as the edges in the triangle they are parallel to.
		face_edges = []
		for triangle in self.simplices[2]:
			inner_edges = []
			for i, outside_edge in enumerate(triangle.faces):
				next_edge = triangle.faces[(i+1) % 3]
				prev_edge = triangle.faces[(i-1) % 3]
				if triangle.face_orientations[i] == 1:
					inner_edges.append(triangulation.add_new_simplex([new_vertices[prev_edge.index], new_vertices[next_edge.index]],
																		[-1, 1]))
				else:
					inner_edges.append(
						triangulation.add_new_simplex([new_vertices[next_edge.index], new_vertices[prev_edge.index]],
																		[-1, 1]))
			face_edges.append(inner_edges)

		# For every tetrahedron, we need to get the three pairs of opposite edges. We do this, by looping over a triangle
		# and then getting the edge
		axes = []
		for tet in self.simplices[3]:
			triangle = tet.faces[0]
			tet_axes = []
			for i in range(3):
				edge = set(triangle.faces).intersection(tet.faces[i+1].faces)
				assert len(edge) == 1
				edge = edge.pop()
				indices = list(range(1, 4))
				indices.remove(i+1)
				opposite_edge = set(tet.faces[indices[0]].faces).intersection(tet.faces[indices[1]].faces)
				assert len(opposite_edge) == 1
				opposite_edge = opposite_edge.pop()
				tet_axes.append([new_vertices[edge.index], new_vertices[opposite_edge.index]])
			axes.append(tet_axes)
		# This is where you choose the axis of the octahedron that you want to split along
		chosen_axes = [item[0] for item in axes]
		axis_edges = []
		for axis in chosen_axes:
			axis_edges.append(triangulation.add_new_simplex([axis[0], axis[1]], [-1, 1]))

		# Each triangle is broken into four pieces, one center triangle, and three triangles which each contain a vertex
		# of the original triangle.
		center_triangles = []
		for triangle in self.simplices[2]:
			faces = [face_edges[triangle.index][triangle.faces.index(triangle.faces[i])] for i in range(3)]
			signs = [-triangle.face_orientations[i] for i in range(3)]
			center_triangles.append(triangulation.add_new_simplex(faces, signs))

		triforce_triangles = []
		# For each vertex on each triangle, we add a new triangle (the three empty triangles in the triforce).
		# These are indexed by the edge which is opposite to them on the triangle
		for triangle in self.simplices[2]:
			triforce_subtriangles = []
			for opposite_edge_index in range(3):
				prev_edge_index, next_edge_index = (opposite_edge_index-1) % 3, (opposite_edge_index+1) % 3
				next_edge = triangle.faces[next_edge_index]
				prev_edge = triangle.faces[prev_edge_index]

				next_edge_sign = triangle.face_orientations[next_edge_index]
				opposite_edge_sign = triangle.face_orientations[opposite_edge_index]
				prev_edge_sign = triangle.face_orientations[prev_edge_index]

				inner_subtriangle_edge = face_edges[triangle.index][opposite_edge_index]

				if next_edge_sign > 0:
					next_subtriangle_edge = edge_front_halves[next_edge.index]
				else:
					next_subtriangle_edge = edge_back_halves[next_edge.index]

				if prev_edge_sign > 0:
					prev_subtriangle_edge = edge_back_halves[prev_edge.index]
				else:
					prev_subtriangle_edge = edge_front_halves[prev_edge.index]

				edges = [prev_subtriangle_edge, inner_subtriangle_edge, next_subtriangle_edge]
				signs = [prev_edge_sign, opposite_edge_sign, next_edge_sign]

				triforce_subtriangles.append(triangulation.add_new_simplex(edges, signs))
			triforce_triangles.append(triforce_subtriangles)

		# For the chosen axis, creates a triangle around the axis and the remaining point on the octahedron.
		axial_triangles = []
		for i, chosen_axis, in enumerate(chosen_axes):
			all_axes = axes[i]
			other_axes = all_axes[:]
			other_axes.remove(chosen_axis)
			tetrahedron = self.simplices[3][i]
			outer_points = other_axes[0] + other_axes[1]
			axis_triangles = []
			for point in outer_points:
				next_triangle = prev_triangle = None
				for triangle in tetrahedron.boundary(2):
					edge_midpoints = [new_vertices[edge.index] for edge in triangle.faces]
					if point in edge_midpoints and chosen_axis[0] in edge_midpoints:
						prev_triangle = triangle
					elif point in edge_midpoints and chosen_axis[1] in edge_midpoints:
						next_triangle = triangle
				assert next_triangle is not None and prev_triangle is not None
				next_edge = prev_edge = None
				for edge in face_edges[next_triangle.index]:
					if point in edge.faces and chosen_axis[1] in edge.faces:
						next_edge = edge
				for edge in face_edges[prev_triangle.index]:
					if point in edge.faces and chosen_axis[0] in edge.faces:
						prev_edge = edge
				assert next_edge is not None and prev_edge is not None
				edges = [axis_edges[i], next_edge, prev_edge]
				index = next_edge.faces.index(chosen_axis[1])
				next_sign = -next_edge.face_orientations[index]
				index = prev_edge.faces.index(chosen_axis[0])
				prev_sign = next_edge.face_orientations[index]
				signs = [1, next_sign, prev_sign]
				axis_triangles.append(triangulation.add_new_simplex(edges, signs))
			axial_triangles.append(axis_triangles)

		# A triangle for each vertex of each tetrahedron which needs to be added as we truncate the tetrahedron
		# The triangles are oriented the same as the parallel faces of the
		# A tetrahedron for each corner of the tetrahedron that we chop off at the above added faces.
		truncation_triangles = []
		corner_tetrahedra = []
		for tetrahedron in self.simplices[3]:
			tetrahedron_truncation_triangles = []
			corner_tetrahedra_this_one = []
			for triangle in tetrahedron.faces:

				# A list of the remaining triangles which are faces of the given tetrahedron, in order of the edges on
				# the current triangle shared by this one.
				other_triangles = []
				for edge in triangle.faces:
					other_triangles_unsorted = [face for face in tetrahedron.faces if face != triangle]
					for other_triangle in other_triangles_unsorted:
						if edge in other_triangle.faces:
							other_triangles.append(other_triangle)
				truncation_triangle_edges = []
				truncation_triangle_signs = []
				for i in range(3):
					index = other_triangles[i].faces.index(triangle.faces[i])
					truncation_triangle_edges.append(face_edges[other_triangles[i].index][index])
					# index = center_triangles[other_triangles[i]].faces.index(other_triangles[i])
					truncation_triangle_signs.append(triangle.face_orientations[i])

				truncation_triangle = triangulation.add_new_simplex(truncation_triangle_edges, truncation_triangle_signs)
				tetrahedron_truncation_triangles.append(truncation_triangle)

				tetrahedron_faces = [truncation_triangle]
				index = tetrahedron.faces.index(triangle)
				tetrahedron_signs = [tetrahedron.face_orientations[index]]
				for i in range(3):
					index = other_triangles[i].faces.index(triangle.faces[i])
					tetrahedron_faces.append(triforce_triangles[other_triangles[i].index][index])
					index = tetrahedron.faces.index(other_triangles[i])
					tetrahedron_signs.append(tetrahedron.face_orientations[index])
				corner_tetrahedra_this_one.append(triangulation.add_new_simplex(tetrahedron_faces, tetrahedron_signs))

			truncation_triangles.append(tetrahedron_truncation_triangles)
			corner_tetrahedra.append(corner_tetrahedra_this_one)

		for i, chosen_axis in enumerate(chosen_axes):
			all_axes = axes[i]
			other_axes = all_axes[:]
			other_axes.remove(chosen_axis)
			# Each pair of points coming one from each other axis, along with the central axis determines a unique
			# tetrahedron after the splitting.
			split_tetrahedra = []
			for axis_1_place, point1 in enumerate(other_axes[0]):
				for axis_2_place, point2 in enumerate(other_axes[1]):
					face1 = axial_triangles[i][axis_1_place]
					face2 = axial_triangles[i][2+axis_2_place]
					faces = [face1, face2]
					signs = [None, None, None, None]
					potential_outside_faces = []
					index = None
					for face in self.simplices[3][i].faces:
						central_face = center_triangles[face.index]
						if point1 in central_face.boundary(0) and point2 in central_face.boundary(0):
							potential_outside_faces.append(central_face)
							index = self.simplices[3][i].faces.index(face)
					assert len(potential_outside_faces) == 1
					# The outside face of each of the octrahedral tetrahedra shares an edge with each of the octahedral
					# triangles and this can be used to determine the orientation of these internal triangles with respect
					# to the tetrahedron. (This code is done simultaneously for both of the internal triangles)
					outside_face = potential_outside_faces[0]
					faces.append(outside_face)
					outside_face_sign = self.simplices[3][i].face_orientations[index]
					signs[2] = outside_face_sign
					first_faces = [face1, face2]
					shared_edges = [set(face.faces).intersection(set(outside_face.faces)) for face in first_faces]
					assert len(shared_edges[0]) == 1
					assert len(shared_edges[1]) == 1
					edges = [edge.pop() for edge in shared_edges]
					indices_on_outside_face = [outside_face.faces.index(edge) for edge in edges]
					face_pairs = [(get_tail(edge), get_head(edge)) for edge in edges]
					indices_on_faces = [first_faces[i].faces.index(edges[i]) for i in range(2)]
					outside_pairs = []
					for j in range(2):
						if outside_face_sign * outside_face.face_orientations[indices_on_outside_face[j]] > 0:
							outside_pairs.append((get_tail(edges[j]), get_head(edges[j])))
						else:
							outside_pairs.append((get_head(edges[j]), get_tail(edges[j])))
					for j, face in enumerate(first_faces):
						if face.face_orientations[indices_on_faces[j]] < 0:
							face_pairs[j] = (face_pairs[j][1], face_pairs[j][0])
						if face_pairs[j] == outside_pairs[j]:
							signs[j] = -1
						else:
							assert face_pairs[j] == (outside_pairs[j][1], outside_pairs[j][0])
							signs[j] = 1
					potential_truncation_triangles = []
					chosen_index = None
					for index, face in enumerate(truncation_triangles[i]):
						if point1 in face.boundary(0) and point2 in face.boundary(0):
							potential_truncation_triangles.append(face)
							chosen_index = index
					assert len(potential_truncation_triangles) == 1
					faces.append(potential_truncation_triangles[0])
					signs[3] = -self.simplices[3][i].face_orientations[chosen_index]
					assert None not in signs
					split_tetrahedra.append(triangulation.add_new_simplex(faces, signs))
		if get_chain_maps:
			F0 = matrix(ZZ, len(triangulation.simplices[0]), len(self.simplices[0]), lambda y, x: x == y)
			F1_1 = matrix(ZZ, len(triangulation.simplices[1]), len(self.simplices[1]), lambda y, x: x == y)
			F1_2 = matrix(ZZ, len(triangulation.simplices[1]), len(self.simplices[1]), lambda y, x: y == x+len(self.simplices[1]))
			F1 = F1_1+F1_2
			F2_1 = matrix(ZZ, len(triangulation.simplices[2]), len(self.simplices[2]), lambda y, x: x == y)
			F2_2 = matrix(ZZ, len(triangulation.simplices[2]), len(self.simplices[2]),
							lambda y, x: x == floor((y-len(self.simplices[2]))/3))
			F2 = F2_1 + F2_2
			F3_1 = matrix(ZZ, len(triangulation.simplices[3]), len(self.simplices[3]), lambda y, x: x == floor(y/4))
			F3_2 = matrix(ZZ, len(triangulation.simplices[3]), len(self.simplices[3]), lambda y, x:
						floor((y-4*len(self.simplices[3]))/4) == x)
			F3 = F3_1 + F3_2
			return triangulation, [F0, F1, F2, F3]
		return triangulation


def get_head(edge):
	"""
	Gets the head of the given one-dimensional simplex. If the given simplex is not 1-dimensional, throws an error.
	"""
	assert edge.dimension() == 1
	index = edge.face_orientations.index(1)
	return edge.faces[index]


def get_tail(edge):
	"""
	Gets the tail of the given one-dimensional simplex. If the given simplex is not 1-dimensional, throws an error.
	"""
	assert edge.dimension() == 1
	index = edge.face_orientations.index(-1)
	return edge.faces[index]


def get_cyclic_vertex_list(triangle):
	"""
	For a triangular simplex where the edges are ordered cyclically, returns a list of the vertices [v_0, v_1, v_2] such
	that v_0, v_1 are vertices of the first edge, v_1, v_2 are vertices of the second edge, v_2, v_0 are vertices of the
	third edge.
	"""
	vertex_tuples = [(edge.faces[0], edge.faces[1]) for edge in triangle.faces]
	for i, sign in enumerate(triangle.face_orientations):
		if sign < 0:
			vertex_tuples[i] = (vertex_tuples[i][1], vertex_tuples[i][0])
	for i in range(3):
		assert vertex_tuples[i][0] == vertex_tuples[(i-1) % 2][1]
	return [tup[0] for tup in vertex_tuples]


def get_opposite_vertex(triangle, edge):
	"""
	Assuming that the triangle's edges are oriented cyclically, gets the vertex which is opposite to the given edge.
	"""
	vertex_list = get_cyclic_vertex_list(triangle)
	index = triangle.faces.index(edge)
	return vertex_list[(index-1) % 2]


