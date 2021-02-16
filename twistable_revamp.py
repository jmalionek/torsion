import math
from typing import List

from sage.all import (RR, ZZ, matrix, DiGraph, ChainComplex, FreeGroup, Graph, vector, AbelianGroup)
import sage
import snappy
import d_domain
import torsion_poly
import random
import examples

# noinspection SpellCheckingInspection
Alphabet = '$abcdefghijklmnopqrstuvwxyzZYXWVUTSRQPONMLKJIHGFEDCBA'


class TwistableDomain(object):

    def __init__(self, dirichlet_domain):
        self.D = dirichlet_domain
        self._setup_holonomy()
        self._setup_vertex_orbits()

        self._setup_edge_orbits()
        print('gets here')
        self._setup_cells()
        print('gets here')
        self._setup_edges()
        print('gets here')
        self._setup_faces()
        self._setup_graphs()
        self.sage_dual_group = None
        self.sage_dual_group_ring = None
        self.abelianization = None

    # ---------------------------SETUP-----------------------
    def _setup_holonomy(self):
        self.holonomy_generators = []
        self.holonomy_inverse_generators = []
        self.all_holonomy = []
        for i, face in enumerate(self.D.face_list()):
            hol = HolonomyElement(face_list=[i])
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
                vertex = Vertex(index=index, holonomy=HolonomyElement([]))
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
                edge = Edge(index=index, holonomy=HolonomyElement([]))
                orbit = EdgeOrbit(preferred=edge, index=orbit_index)
                orbit.add(edge)
                self.edges[index] = edge
                self.edge_orbits[orbit_index] = orbit

    def _setup_cells(self):
        while None in self.vertices:
            print('in while')
            # see where the edges and vertices are glued to across the faces for each face
            for face_index, face in enumerate(self.D.face_list()):
                # where are vertices glued
                for index, vertex_index in enumerate(face['vertex_indices']):
                    if self.vertices[vertex_index] is not None:
                        glued_index = face['vertex_image_indices'][index]
                        if self.vertices[glued_index] is None:
                            # ORIGINALLY
                            # glued_vertex = self.all_holonomy[face_index].inverse().apply(self.vertices[vertex_index])

                            glued_vertex = self.all_holonomy[face_index].inverse().apply(self.vertices[vertex_index])
                            glued_vertex.index = glued_index
                            self.vertices[glued_index] = glued_vertex
        while None in self.edges:
            for face_index, face in enumerate(self.D.face_list()):
                # where are edges glued
                for index, edge_index in enumerate(face['edge_indices']):
                    if self.edges[edge_index] is not None:
                        glued_index = face['edge_image_indices'][index]
                        if self.edges[glued_index] is None:
                            # ORIGINALLY
                            # glued_edge = self.all_holonomy[face_index].apply(self.edges[edge_index])
                            glued_edge = self.all_holonomy[face_index].inverse().apply(self.edges[edge_index])
                            glued_edge.index = glued_index
                            self.edges[glued_index] = glued_edge

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
                face = Face(None, HolonomyElement(face_list=[]), vertices[::-1], edges[::-1], paired_vertices[::-1],
                            paired_edges[::-1], [x * (-1) for x in signs], index=i)
            # face = Face(None,HolonomyElement([]),vertices,edges,paired_vertices,paired_edges, edge_orientations = signs,index = i)
            else:
                signs = face_dict['edge_orientations']
                # We want the holonomy to preserve the orientation of the cells
                # We work under the assumption that all 3 cells are oriented outward
                # i.e. the induced orientation on the faces follows a right hand rule
                face = Face(None, HolonomyElement([i]), vertices, edges, paired_vertices, paired_edges,
                            edge_orientations=signs, index=i)
            # face = Face(None, HolonomyElement(face_list = [i]),vertices[::-1],edges[::-1],paired_vertices[::-1],paired_edges[::-1],[x*(-1) for x in signs], index = i)
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
        edges = [(edge.tail, edge.head, edge) for edge in self.edges]
        edge_orbits = [(edge.tail, edge.head, edge) for edge in self.edge_orbits]
        self.digraph = DiGraph([[vertex for vertex in self.vertices], edges], loops=True, multiedges=True)
        self.orbit_digraph = DiGraph([self.vertex_orbits, edge_orbits], loops=True, multiedges=True)
        self.graph = self.digraph.to_undirected()
        self.orbit_graph = self.orbit_digraph.to_undirected()
        spanning_tree = self.orbit_graph.min_spanning_tree(starting_vertex=self.vertex_orbits[0], algorithm='Boruvka')
        self.spanning_tree = [edge[2] for edge in spanning_tree]
        self.essential_edge_orbits = [edge for edge in self.edge_orbits if edge not in self.spanning_tree]
        self.spanning_tree_graph = Graph([self.vertex_orbits, spanning_tree])

    def shortest_path_in_orbit_tree(self, v0, v1, report_vertices=False):
        paths = sage.graphs.path_enumeration.all_paths(self.spanning_tree_graph, v0, v1, report_edges=True, labels=True)
        assert len(paths) == 1
        if report_vertices:
            return paths[0]
        else:
            return [edge[2] for edge in paths[0]]

    # assumes that no edge in the vertex path has same head and tail
    def path_lift(self, edge_path, starting_vertex, report_vertices=True, report_edges=False):
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
            if edge_orient_from_inside_face0 != 1:
                first_face = face0
                last_face = face1
            else:
                first_face = face1
                last_face = face0
            holonomy = HolonomyElement([])
            current_face = first_face
            current_edge = edge
            nextface = current_face.paired_face
            nextedge = None
            while nextedge != edge:
                # ORIGINAL
                # holonomy = holonomy.compose(HolonomyElement(face_list = [current_face.index]))
                # NEW ONE (THIS ONE MAKES MORE SENSE)
                holonomy = HolonomyElement(face_list=[current_face.index]).compose(holonomy)
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
            relations.append(holonomy.inverse())
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
        U = U[num_ones:]
        self.abelianization = AbelianGroup(diag[num_ones:] + [0, ] * (m - d))
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
        self.abelianization_ring = self.abelianization.algebra(ZZ)

        def phi2(hol):
            return self.abelianization_ring(phi(hol))

        return phi2

    def dual_abelianization_ring(self):
        if self.abelianization is None:
            self.map_to_dual_abelianization_ring()
        return self.abelianization_ring

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

    def _setup_boundaries(self, phi=None, ring=ZZ, dimension=1, identity=None, as_list=False):
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
            face = self.face_orbits[j]
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
            head_orbit = edge_orbit.head
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
            b.append(hols[1] - hols[0])
        if as_list:
            return b
        if dimension == 1:
            return matrix(ring, codomain_dimension, domain_dimension, b)
        else:
            return matrix.block(ring, codomain_dimension, domain_dimension, [a.transpose() for a in b], subdivide=True)


# ---------------------------------Cell Classes------------------------------------
# --------------Abstract Cells---------------
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


# ---------------Cells and Orbits-----------

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


# ---------------Concrete Cells--------------
class Vertex(Cell, AbstractVertex):
    def __init__(self, orbit=None, holonomy=None, index=None):
        Cell.__init__(self, orbit, holonomy, index)
        AbstractVertex.__init__(self)

    def index(self):
        return self.index

    def __str__(self):
        return '{0}(V{1})'.format(self.holonomy.holonomy, str(self.orbit.index))


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


# ~ class AbstractPolyhedron(object):
# ~ def __init__(self, index, faces = None, face_orientations = None):
# ~ self.index = index
# ~ if faces == None:
# ~ self.faces = []
# ~ else:
# ~ self.faces = faces
# ~ self.face_orientations = face_orientations

# ~ class Polyhedron(Cell, AbstractPolyhedron):
# ~ def __init__
# ~ AbstractPolyhedron.__init__(index)

# ~ class PolyhedronOrbit(CellClass,AbstractPolyhedron):
# ~ pass


# ----------------------------------Holonomy----------------------------------

# THIS WHAT MAKES IT OP
# Throughout this program, we are using the convention that (cell)[a,b,c]=c(b(a(cell)))
class HolonomyElement(object):
    def __init__(self, tietze=None, face_list=None):
        if face_list is not None:
            self.holonomy = self.Tietze(face_list)
        if tietze is not None:
            self.holonomy = tietze
        while self.reduce():
            pass

    def __str__(self):
        return 'Hol{0}'.format(self.holonomy)

    def Tietze(self, faces):
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
        return HolonomyElement(hol.holonomy + self.holonomy)

    def inverse(self):
        return HolonomyElement([-i for i in self.holonomy[::-1]])

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

    def __getitem__(self, key):
        if (isinstance(key, tuple)):
            if len(key) > 1:
                raise IndexError('HolonomyElement does not support multiple indexing')
            else:
                key = key[0]
        elif (isinstance(key, slice)):
            return HolonomyElement(self.holonomy[key])
        return HolonomyElement([self.holonomy[key]])

    def __eq__(self, other):
        if not isinstance(other, HolonomyElement):
            print('goes hee')
            return False
        else:
            return self.holonomy == other.holonomy


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


def phi_from_Tietze_mapping(mapping, identity=1):
    def phi(hol):
        out = identity
        for i in hol.holonomy:
            # original
            out = out * mapping(i)
        return out

    return phi


def phi_from_face_mapping(mapping, identity=1):
    def t_mapping(i):
        sign = 1 if i < 0 else 0
        i = 2 * (abs(i) - 1) + sign
        if hasattr(mapping, '__getitem__'):
            return mapping[i]
        else:
            return mapping(i)

    return phi_from_Tietze_mapping(t_mapping, identity)


def equal_matrices(A, B, tol=.0001):
    return (A - B).norm('frob') < tol


# ~ class GroupRingTerm(object):
# ~ def __init__(self,coeff,face_list):
# ~ self.coeff = coeff
# ~ self.face_list = face_list)


# -----------------------------Testing-------------------------------

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
    DD = TwistableDomain(D)
    torsion_poly.enhance_domain(D)
    # print(torsion_poly.get_relations(D,False))
    # print([hol.as_face_list() for hol in DD.get_dual_relations()])
    for i in range(10):
        M = random.choice(snappy.OrientableClosedCensus)
        D = M.dirichlet_domain()
        DD = TwistableDomain(D)
        torsion_poly.enhance_domain(D)
        # print(DD.dual_fundamental_group().abelian_invariants())
        print(M.homology())
        assert torsion_poly.sage_fundamental_group(D,
                                                   False).abelian_invariants() == DD.dual_fundamental_group().abelian_invariants()


# WARNING: d_domain.py will usually throw a bunch of errors due to imprecision in this test
# To fix, comment out the following line in d_domain
# assert mp.mnorm(point - match) < 5000*mp.eps, ('Point match', mp.mnorm(point - match), 5000*mp.eps)
# to stop these errors
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
        M = random.choice(snappy.OrientableClosedCensus)
        D = M.dirichlet_domain()
        DD = TwistableDomain(D)
        NathanD = d_domain.FundamentalDomain(D)
        assert (equal_matrices(DD.dualB2().smith_form()[0].transpose(), NathanD.B2().smith_form()[0]))
        assert (equal_matrices(DD.dualB3().smith_form()[0].transpose(), NathanD.B1().smith_form()[0]))
        assert (equal_matrices(DD.dualB2() * DD.dualB3(), 0))
        print('{0} tests good'.format(i + 1))


# WARNING: d_domain.py will usually throw a bunch of errors due to imprecision in this test
# To fix, comment out the following line in d_domain
# assert mp.mnorm(point - match) < 5000*mp.eps, ('Point match', mp.mnorm(point - match), 5000*mp.eps)
# to stop these errors
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
            M = random.choice(snappy.OrientableClosedCensus)
            D = M.dirichlet_domain()
            DD = TwistableDomain(D)
            NathanD = d_domain.FundamentalDomain(D)
            assert DD.reduced_dualB2().smith_form()[0].diagonal(), NathanD.B2().smith_form()[0].diagonal()
            assert DD.reduced_dualB3().smith_form()[0].diagonal(), NathanD.B1().smith_form()[0].diagonal()
            assert equal_matrices(DD.dualB2() * DD.dualB3(), 0)
            print('{0} tests good'.format(i + 1))


def save_graphs(D, string):
    DD = TwistableDomain(D)
    DD.orbit_digraph.plot(edge_labels=True).save('./pictures'+string + '_orbit_digraph.png')
    DD.orbit_graph.plot(edge_labels=True).save('./pictures'+string + '_orbit_graph.png')
    DD.digraph.plot(edge_labels=True).save('./pictures'+string + '_digraph.png')
    DD.graph.plot(edge_labels=True).save('./pictures'+string + '_graph.png')


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


# tests the twisted boundary maps, using the O(3,1) representation of the fundamental group from snappy
def test_twisted_boundaries(D):
    DD = TwistableDomain(D)
    phi = phi_from_face_mapping(D.pairing_matrices())
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
    print('d2\n\n\n')
    print(DD.dualB2(phi=phi, ring=RR, dimension=4).n(digits=3))
    print('d3\n\n\n')
    print(DD.dualB3(phi=phi, ring=RR, dimension=4).n(digits=3))


def test_abelianization(M, D):
    DD = TwistableDomain(D)
    print(DD.fundamental_group_abelianization())
    print(M.homology())
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


# Tests on the genus 2 surface with the presentation <a,b,c,d|aBAbcDCd>
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


def test_Seifert_Weber():
    D = examples.Seifert_Weber_Structure()
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


if __name__ == '__main__':
    # M = snappy.OrientableClosedCensus[0]
    M = snappy.Manifold('m160(-3, 2)')
    # M = random.choice(snappy.OrientableClosedCensus(betti = 1))
    M = random.choice(snappy.OrientableClosedCensus)
    D = M.dirichlet_domain()
    DD = TwistableDomain(D)
    # NathanD = d_domain.FundamentalDomain(D)
    # test_boundaries(D)
    # test_fundamental_group(D)
    # test_dual_boundaries(D)
    # test_graphs(D)
    # test_reduced_boundaries(D)
    # test_twisted_boundaries(D)
    #save_graphs(D, 'snappy_seif_vape_dodec')
    # test_boundaries_abelianized_group_ring(D)
    # test_boundaries_abelianized_group_ring(D=examples.Seifert_Weber_Structure())
    # test_abelianization(M,D)
    # three_torus_testing()
    # test_noncommatative_group_ring_genus2()
    # test_noncommatative_group_ring(D)
    # test_Seifert_Weber()
    # print(DD.B2().smith_form()[0]==(NathanD.B2().smith_form()[0]))
    # SEIFERT WEBER EXAMPLES
    if False:
        test_Seifert_Weber()
        test_boundaries_abelianized_group_ring(D=examples.Seifert_Weber_Structure())
    elif True:
        test_twisted_boundaries(D)
        test_noncommutative_group_ring(D)
        test_boundaries_abelianized_group_ring(D)

# TODO MAKE THINGS ORIENTED OUTWARDS??
# FIGURE OUT ORIENTATIONS AND SPECIFICS OF DUAL CELLS

# sage -pip install git+https://github.com/3-Manifolds/SnapPy

# Lin and Lipnowski paper
# https://arxiv.org/pdf/2003.11165.pdf
