from compiler.program import Program, CommonPreprocessedInput
from utils import *
from enum import Enum
from curve import get_roots_of_unity
from setup import *
from typing import Optional
from dataclasses import dataclass
from transcript import Transcript, Message1, Message2, Message3, Message4, Message5
from poly import Polynomial, Basis

class Column(Enum):
    LEFT = 1
    RIGHT = 2
    OUTPUT = 3

@dataclass
class Proof:
    msg_1: Message1
    msg_2: Message2
    msg_3: Message3
    msg_4: Message4
    msg_5: Message5

    def flatten(self):
        proof = {}
        proof["a_1"] = self.msg_1.a_1
        proof["b_1"] = self.msg_1.b_1
        proof["c_1"] = self.msg_1.c_1
        proof["z_1"] = self.msg_2.z_1
        proof["t_lo_1"] = self.msg_3.t_lo_1
        proof["t_mid_1"] = self.msg_3.t_mid_1
        proof["t_hi_1"] = self.msg_3.t_hi_1
        proof["a_eval"] = self.msg_4.a_eval
        proof["b_eval"] = self.msg_4.b_eval
        proof["c_eval"] = self.msg_4.c_eval
        proof["s1_eval"] = self.msg_4.s1_eval
        proof["s2_eval"] = self.msg_4.s2_eval
        proof["z_shifted_eval"] = self.msg_4.z_shifted_eval
        proof["W_z_1"] = self.msg_5.W_z_1
        proof["W_zw_1"] = self.msg_5.W_zw_1
        return proof


@dataclass
class Prover:
    group_order: int
    setup: Setup
    program: Program
    pk: CommonPreprocessedInput

    def __init__(self, setup: Setup, program: Program):
        self.group_order = program.group_order
        self.setup = setup
        self.program = program
        self.pk = program.common_preprocessed_input()

    def prove(self, witness: dict[Optional[str], int]) -> Proof:
        # Initialise Fiat-Shamir transcript
        transcript = Transcript(b"plonk")

        # Collect fixed and public information
        # FIXME: Hash pk and PI into transcript

        # witness = {"a": 3, "b": 4, "c": 12, "d": 5, "e": 60}
        # public_vars = ["e"]
        public_vars = self.program.get_public_assignments()
        PI = Polynomial(
            [Scalar(-witness[v]) for v in public_vars]
            + [Scalar(0) for _ in range(self.group_order - len(public_vars))],
            Basis.LAGRANGE,
        )
        self.PI = PI

        # Round 1
        msg_1 = self.round_1(witness)
        self.beta, self.gamma = transcript.round_1(msg_1)

        # Round 2
        msg_2 = self.round_2()
        self.alpha, self.fft_cofactor = transcript.round_2(msg_2)

        # Round 3
        msg_3 = self.round_3()
        self.zeta = transcript.round_3(msg_3)

        # Round 4
        msg_4 = self.round_4()
        self.v = transcript.round_4(msg_4)

        # Round 5
        msg_5 = self.round_5()

        return Proof(msg_1, msg_2, msg_3, msg_4, msg_5)

    def round_1(
        self,
        witness: dict[Optional[str], int],
    ) -> Message1:
        program = self.program
        setup = self.setup
        group_order = self.group_order

        if None not in witness:
            witness[None] = 0

        # Compute wire assignments for A, B, C, corresponding:
        # - A_values: witness[program.wires()[i].L]
        # - B_values: witness[program.wires()[i].R]
        # - C_values: witness[program.wires()[i].O]
        A_values = [Scalar(0) for _ in range(group_order)]
        B_values = [Scalar(0) for _ in range(group_order)]
        C_values = [Scalar(0) for _ in range(group_order)]

        for i in range(len(program.wires())):    
            A_values[i] = Scalar(witness[program.wires()[i].L])
            B_values[i] = Scalar(witness[program.wires()[i].R])
            C_values[i] = Scalar(witness[program.wires()[i].O])
        
        A_evals = Polynomial(list(A_values),Basis.LAGRANGE)
        B_evals = Polynomial(list(B_values),Basis.LAGRANGE)
        C_evals = Polynomial(list(C_values),Basis.LAGRANGE)

        A_pt = self.setup.commit(A_evals)
        B_pt = self.setup.commit(B_evals)
        C_pt = self.setup.commit(C_evals)

        # self.A = A_evals.evals_to_coeffs()
        # self.B = B_evals.evals_to_coeffs()
        # self.C = C_evals.evals_to_coeffs()
        self.A = A_evals
        self.B = B_evals
        self.C = C_evals

        # Construct A, B, C Lagrange interpolation polynomials for
        # A_values, B_values, C_values

        # Compute a_1, b_1, c_1 commitments to A, B, C polynomials

        # Sanity check that witness fulfils gate constraints
        assert (
            self.A * self.pk.QL
            + self.B * self.pk.QR
            + self.A * self.B * self.pk.QM
            + self.C * self.pk.QO
            + self.PI
            + self.pk.QC
            == Polynomial([Scalar(0)] * group_order, Basis.LAGRANGE)
        )

        # Return a_1, b_1, c_1
        a_1 = A_pt
        b_1 = B_pt
        c_1 = C_pt
        return Message1(a_1, b_1, c_1)

    def round_2(self) -> Message2:
        group_order = self.group_order
        setup = self.setup

        # Using A, B, C, values, and pk.S1, pk.S2, pk.S3, compute
        # Z_values for permutation grand product polynomial Z
        #
        # Note the convenience function:
        #       self.rlc(val1, val2) = val_1 + self.beta * val_2 + gamma
        # Check that the last term Z_n = 1

    
        SL = self.pk.S1
        SR = self.pk.S2
        SO = self.pk.S3

        Z_values = [Scalar(1)] # Z_0 = 1 
        roots_of_unity = Scalar.roots_of_unity(group_order)
        self.roots_of_unity = roots_of_unity
        for i in range(group_order):
            # Z_{i+1} = Z_i * (f(i)) / (g(i))
            # Z_1 = Z_0 * (f(1)) / (g(1))
            # Z_n = Z_{n-1} * (f(n-1)) / (g(n-1))
            Z_values.append(
                Z_values[-1] * #  Z_values[-1] respresents Z_i 
                (self.A.values[i] + self.beta * 1 * roots_of_unity[i] + self.gamma) * 
                (self.B.values[i] + self.beta * 2 * roots_of_unity[i] + self.gamma) * 
                (self.C.values[i] + self.beta * 3 * roots_of_unity[i] + self.gamma) /
                (self.A.values[i] + self.beta * SL.values[i] + self.gamma) /  # you can view code at utils.Cell::label
                (self.B.values[i] + self.beta * SR.values[i] + self.gamma) / 
                (self.C.values[i] + self.beta * SO.values[i] + self.gamma)
            )
        # Sanity-check Z_n == 1 
        assert Z_values.pop() == 1 

        # Sanity-check that Z was computed correctly
        # (f(X) / g(X)) * z(X) == z(Xw)   
        for i in range(group_order):
            assert (
                self.rlc(self.A.values[i], roots_of_unity[i])
                * self.rlc(self.B.values[i], 2 * roots_of_unity[i])
                * self.rlc(self.C.values[i], 3 * roots_of_unity[i])
            ) * Z_values[i] - (
                self.rlc(self.A.values[i], self.pk.S1.values[i])
                * self.rlc(self.B.values[i], self.pk.S2.values[i])
                * self.rlc(self.C.values[i], self.pk.S3.values[i])
            ) * Z_values[
                (i + 1) % group_order
            ] == 0

        # Construct Z, Lagrange interpolation polynomial for Z_values
        self.Z = Polynomial(Z_values,Basis.LAGRANGE)
        # Cpmpute z_1 commitment to Z polynomial
        z_1 = self.Z.evals_to_coeffs().coeffs_to_point(self.setup.powers_of_x)
        # Return z_1
        return Message2(z_1)

    def round_3(self) -> Message3:
        group_order = self.group_order
        setup = self.setup

        # Compute the quotient polynomial
        
        # List of roots of unity at 4x fineness, i.e. the powers of µ
        # where µ^(4n) = 1
        quarter_roots = Scalar.roots_of_unity(self.group_order * 4)

        # Using self.fft_expand, move A, B, C into coset extended Lagrange basis
        A_big = self.fft_expand(self.A)
        B_big = self.fft_expand(self.B)
        C_big = self.fft_expand(self.C)
        # Expand public inputs polynomial PI into coset extended Lagrange
        PI_big = self.fft_expand(self.PI)
        self.PI_big = PI_big
        # Expand selector polynomials pk.QL, pk.QR, pk.QM, pk.QO, pk.QC
        # into the coset extended Lagrange basis
        QL_big = self.fft_expand(self.pk.QL)
        QR_big = self.fft_expand(self.pk.QR)
        QM_big = self.fft_expand(self.pk.QM)
        QO_big = self.fft_expand(self.pk.QO)
        QC_big = self.fft_expand(self.pk.QC)
        self.QL_big = QL_big 
        self.QR_big = QR_big 
        self.QM_big = QM_big 
        self.QO_big = QO_big 
        self.QC_big = QC_big 
        # Expand permutation grand product polynomial Z into coset extended
        # Lagrange basis
        Z_big = self.fft_expand(self.Z)
        self.Z_big = Z_big
        # Expand shifted Z(ω) into coset extended Lagrange basis
        Z_n_plus_1_valuse = Z_big.values[4:] + Z_big.values[:4]
        Z_shifted_big = Polynomial(Z_n_plus_1_valuse,Basis.LAGRANGE)
        # Expand permutation polynomials pk.S1, pk.S2, pk.S3 into coset
        # extended Lagrange basis
        S1_big = self.fft_expand(self.pk.S1)
        S2_big = self.fft_expand(self.pk.S2)
        S3_big = self.fft_expand(self.pk.S3)
        self.S3_big = S3_big
        # Compute Z_H = X^N - 1, also in evaluation form in the coset
        ZH_big = Polynomial(
            [
                ((Scalar(r) * self.fft_cofactor) ** group_order - 1)
                for r in quarter_roots
            ],
            Basis.LAGRANGE
        )


        # Compute L0, the Lagrange basis polynomial that evaluates to 1 at x = 1 = ω^0
        # and 0 at other roots of unity

        # Expand L0 into the coset extended Lagrange basis
        # L0(0) = 1 , L0(others) = 0
        L0_big = self.fft_expand(
            Polynomial([Scalar(1)] + [Scalar(0)] * (group_order - 1), Basis.LAGRANGE)
        )
        self.L0_big = L0_big
        # Compute the quotient polynomial (called T(x) in the paper)
        # It is only possible to construct this polynomial if the following
        # equations are true at all roots of unity {1, w ... w^(n-1)}:
        # 1. All gates are correct:
        #    A * QL + B * QR + A * B * QM + C * QO + PI + QC = 0
        #
        # 2. The permutation accumulator is valid:
        #    Z(wx) = Z(x) * (rlc of A, X, 1) * (rlc of B, 2X, 1) *
        #                   (rlc of C, 3X, 1) / (rlc of A, S1, 1) /
        #                   (rlc of B, S2, 1) / (rlc of C, S3, 1)
        #    rlc = random linear combination: term_1 + beta * term2 + gamma * term3
        #
        # 3. The permutation accumulator equals 1 at the start point
        #    (Z - 1) * L0 = 0
        #    L0 = Lagrange polynomial, equal at all roots of unity except 1

        
        # for i in range(4 * group_order):
        #     assert (
        #         A_big.values[i] * QL_big.values[i] + B_big.values[i] * QR_big.values[i] + A_big.values[i] * B_big.values[i] * QM_big.values[i] +
        #         C_big.values[i] * QO_big.values[i] + PI_big.values[i] + QC_big.values[i] == 0
        #     )

        # gates_poly = [ 
        #         A_big[i] * QL_big[i] +
        #         B_big[i] * QR_big[i] +
        #         A_big[i] * B_big[i] * QM_big[i] +
        #         C_big[i] * QO_big[i] + 
        #         PI_big[i] +
        #         QC_big[i]
        #         for i in range(self.group_order * 4)
        #         ]

        QUOT_big_points = [
                (
                    (
                        A_big.values[i] * QL_big.values[i] +
                        B_big.values[i] * QR_big.values[i] +
                        A_big.values[i] * B_big.values[i] * QM_big.values[i] +
                        C_big.values[i] * QO_big.values[i] + 
                        PI_big.values[i] +
                        QC_big.values[i]
                    )  +
                    self.alpha * (
                            (
                                (A_big.values[i] + self.beta * 1 * self.fft_cofactor * quarter_roots[i] + self.gamma) *
                                (B_big.values[i] + self.beta * 2 * self.fft_cofactor * quarter_roots[i] + self.gamma) *
                                (C_big.values[i] + self.beta * 3 * self.fft_cofactor * quarter_roots[i] + self.gamma)
                            ) *Z_big.values[i] - 
                            (
                                (A_big.values[i] + self.beta * S1_big.values[i] + self.gamma) *
                                (B_big.values[i] + self.beta * S2_big.values[i] + self.gamma) *
                                (C_big.values[i] + self.beta * S3_big.values[i] + self.gamma)
                            ) *Z_shifted_big.values[i]
                        ) 
                    + 
                    self.alpha ** 2(
                        (Z_big.values[i]-1) * L0_big.values[i] 
                    )
                ) / ZH_big.values[i] 
            for i in range(self.group_order * 4)
        ]
        
        QUOT_big = Polynomial(QUOT_big_points,Basis.LAGRANGE)
        # Sanity check: QUOT has degree < 3n
        assert (
            self.expanded_evals_to_coeffs(QUOT_big).values[-group_order:]
            == [0] * group_order
        )
        print("Generated the quotient polynomial")

        QUOT_big_coeffs = self.expanded_evals_to_coeffs(QUOT_big)
        T1 =  Polynomial(QUOT_big_coeffs.values[:group_order],QUOT_big_coeffs.basis).fft() # evaluation points polynomial
        T2 =  Polynomial(QUOT_big_coeffs.values[group_order: 2 * group_order],QUOT_big_coeffs.basis).fft() # evaluation points polynomial
        T3 =  Polynomial(QUOT_big_coeffs.values[2 * group_order:3 * group_order],QUOT_big_coeffs.basis).fft() # evaluation points polynomial
        self.T1 = T1 
        self.T2 = T2 
        self.T3 = T3 
        # Split up T into T1, T2 and T3 (needed because T has degree 3n - 4, so is
        # too big for the trusted setup)

        # Sanity check that we've computed T1, T2, T3 correctly
        # TODO: Why ?
        assert (
            T1.barycentric_eval(self.fft_cofactor)
            + T2.barycentric_eval(self.fft_cofactor) * self.fft_cofactor ** group_order
            + T3.barycentric_eval(self.fft_cofactor) * self.fft_cofactor ** (group_order * 2)
        ) == QUOT_big.values[0]

        print("Generated T1, T2, T3 polynomials")

        # Compute commitments t_lo_1, t_mid_1, t_hi_1 to T1, T2, T3 polynomials
        t_lo_1 = T1.evals_to_coeffs().coeffs_to_point(self.setup.powers_of_x)
        t_mid_1 = T2.evals_to_coeffs().coeffs_to_point(self.setup.powers_of_x)
        t_hi_1 = T3.evals_to_coeffs().coeffs_to_point(self.setup.powers_of_x)
        # Return t_lo_1, t_mid_1, t_hi_1
        return Message3(t_lo_1, t_mid_1, t_hi_1)

    def round_4(self) -> Message4:
        # Compute evaluations to be used in constructing the linearization polynomial.

        # Compute a_eval = A(zeta)
        self.a_eval = self.A.barycentric_eval(self.zeta)
        # Compute b_eval = B(zeta)
        self.b_eval = self.B.barycentric_eval(self.zeta)
        # Compute c_eval = C(zeta)
        self.c_eval = self.C.barycentric_eval(self.zeta)
        # Compute s1_eval = pk.S1(zeta)
        self.s1_eval = self.pk.S1.barycentric_eval(self.zeta)
        # Compute s2_eval = pk.S2(zeta)
        self.s2_eval = self.pk.S2.barycentric_eval(self.zeta)
        # Compute z_shifted_eval = Z(zeta * ω)
        self.z_shifted_eval = self.Z.barycentric_eval(self.zeta * self.roots_of_unity[1])

        # Return a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval
        return Message4(self.a_eval, self.b_eval, self.c_eval, self.s1_eval, self.s2_eval, self.z_shifted_eval)

    def round_5(self) -> Message5:
        # Evaluate the Lagrange basis polynomial L0 at zeta
        # Evaluate the vanishing polynomial Z_H(X) = X^n - 1 at zeta

        # Move T1, T2, T3 into the coset extended Lagrange basis
        T1_big = self.fft_expand(self.T1)
        T2_big = self.fft_expand(self.T2)
        T3_big = self.fft_expand(self.T3)
        # Move pk.QL, pk.QR, pk.QM, pk.QO, pk.QC into the coset extended Lagrange basis
        QL_big = self.QL_big
        QR_big = self.QR_big
        QM_big = self.QM_big
        QO_big = self.QO_big
        QC_big = self.QC_big
        # Move Z into the coset extended Lagrange basis
        Z_big = self.Z_big
        # Move pk.S3 into the coset extended Lagrange basis
        S3_big = self.fft_expand(self.pk.S3)
        # Compute the "linearization polynomial" R. This is a clever way to avoid
        # needing to provide evaluations of _all_ the polynomials that we are
        # checking an equation betweeen: instead, we can "skip" the first
        # multiplicand in each term. The idea is that we construct a
        # polynomial which is constructed to equal 0 at Z only if the equations
        # that we are checking are correct, and which the verifier can reconstruct
        # the KZG commitment to, and we provide proofs to verify that it actually
        # equals 0 at Z
        #
        # In order for the verifier to be able to reconstruct the commitment to R,
        # it has to be "linear" in the proof items, hence why we can only use each
        # proof item once; any further multiplicands in each term need to be
        # replaced with their evaluations at Z, which do still need to be provided

        PI_eval = self.PI_big.barycentric_eval(self.zeta)
        L0_eval = self.L0_big.barycentric_eval(self.zeta)
        ZH_ev = self.zeta ** self.group_order - 1 # the same to self.zeta/4 ** self.group_order*4
        
        gate_evals = [(
            self.a_eval * self.b_eval * self.QM_big.values[i] +
            self.a_eval * self.QL_big.values[i] +
            self.b_eval * self.QR_big.values[i] + 
            self.c_eval * self.QO_big.values[i] + 
            PI_eval +
            self.QC_big.values[i]
        ) for i in range(4 * self.group_order)]

        permutation_evals = [
            (
                (self.a_eval + self.beta * 1 * self.zeta + self.gamma) *
                (self.b_eval + self.beta * 2 * self.zeta + self.gamma) *
                (self.c_eval + self.beta * 3 * self.zeta + self.gamma) * 
                self.Z_big.values[i] 
            )
            - 
            (
                (self.a_eval + self.beta * self.s1_eval + self.gamma) * 
                (self.b_eval + self.beta * self.s2_eval + self.gamma) * 
                (self.c_eval + self.beta * self.S3_big.values[i] + self.gamma) *
                self.z_shifted_eval       
            )for i in range(4 * self.group_order)
        ]

    
        R_big_evals = [
        (
            gate_evals[i]
            +
            self.alpha * (permutation_evals[i]) 
            +
            self.alpha**2 * ((self.Z_big.values[i] - 1)* L0_eval) 
            - 
            (
                ZH_ev*
                (
                    T1_big.values[i] + 
                    self.zeta**self.group_order * T2_big.values[i] +
                    self.zeta**(self.group_order*2) * T3_big.values[i] 
                )
            )
        )
        for i in range(4 * self.group_order)   
        ]

        R_big = Polynomial(R_big_evals,Basis.LAGRANGE)

        # check R Order
        R_coeffs = self.expanded_evals_to_coeffs(R_big)
        assert R_coeffs.values[self.group_order:] == [0] * (self.group_order * 3)
        R_coeffs = Polynomial( R_coeffs.values[:self.group_order],Basis.MONOMIAL)

        # print(sum([R_coeffs.values[i] * self.zeta**i for i in range(self.group_order)]))
        # assert 0 == sum([R_coeffs.values[i] * self.zeta**i for i in range(self.group_order)])

        # Commit to R
        R = R_coeffs.fft() 
        R_pt = self.setup.commit(R)
        
        # Sanity-check R

        # assert R_big.barycentric_eval(self.zeta) == 0
        assert R.barycentric_eval(self.zeta) == 0

        print("Generated linearization polynomial R")


        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct
        group_order = self.group_order
        quarter_roots = Scalar.roots_of_unity(group_order * 4)    
        W_z_big = [(
            R_big.values[i] + 
            self.v * (self.fft_expand(self.A).values[i] - self.a_eval) + 
            self.v**2 * (self.fft_expand(self.B).values[i] - self.b_eval) +
            self.v**3 * (self.fft_expand(self.C).values[i] - self.c_eval) + 
            self.v**4 * (self.fft_expand(self.pk.S1).values[i] - self.s1_eval) +
            self.v**5 * (self.fft_expand(self.pk.S2).values[i] - self.s2_eval) 
        ) / (self.fft_cofactor * quarter_roots[i] - self.zeta) for i in range(self.group_order *4)]
        # TODO: why is ru[i] - zeta 

        # Move A, B, C into the coset extended Lagrange basis
        # Move pk.S1, pk.S2 into the coset extended Lagrange basis

        # In the COSET EXTENDED LAGRANGE BASIS,
        # Construct W_Z = (
        #     R
        #   + v * (A - a_eval)
        #   + v**2 * (B - b_eval)
        #   + v**3 * (C - c_eval)
        #   + v**4 * (S1 - s1_eval)
        #   + v**5 * (S2 - s2_eval)
        # ) / (X - zeta)

        W_z_big = Polynomial[W_z_big,Basis.LAGRANGE]
        W_z_coeffs = self.expanded_evals_to_coeffs(W_z_big)
        # Check that degree of W_z is not greater than n
        assert W_z_coeffs.values[group_order:] == [0] * (group_order * 3)

        # Compute W_z_1 commitment to W_z
        W_z_1 = self.setup.commit(W_z_coeffs.fft())

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.
        # In other words: Compute W_zw = (Z - z_shifted_eval) / (X - zeta * ω)

        roots_of_unity = Scalar.roots_of_unity(self.group_order)
        W_zw_big_points = [
            (Z_big[i] - self.z_shifted_eval) / 
            (self.fft * quarter_roots[i] - self.zeta * roots_of_unity[1])
        for i in range(self.group_order * 4)
        ]

        W_zw_big = Polynomial(W_zw_big_points,Basis.LAGRANGE)
        W_zw_coeffs = W_zw_big.evals_to_coeffs()

        # Check that degree of W_z is not greater than n
        assert W_zw_coeffs.values[group_order:] == [0] * (group_order * 3)

        # Compute W_zw_1 commitment to W_zw
        W_zw_1 = self.setup.commit(W_zw_coeffs.fft())
        print("Generated final quotient witness polynomials")

        # Return W_z_1, W_zw_1
        return Message5(W_z_1, W_zw_1)

    def fft_expand(self, x: Polynomial):
        return x.to_coset_extended_lagrange(self.fft_cofactor)

    def expanded_evals_to_coeffs(self, x: Polynomial):
        return x.coset_extended_lagrange_to_coeffs(self.fft_cofactor)

    def rlc(self, term_1, term_2):
        return term_1 + term_2 * self.beta + self.gamma
