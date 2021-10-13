import math

from sage.all import RR, vector

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


class Polyhedron(Cell, AbstractPolyhedron):
	def __init__(self, faces, orbit=None, holonomy=None, index=None):
		CellClass.__init__(self, orbit, holonomy, index)
		AbstractPolyhedron.__init__(self, faces)
