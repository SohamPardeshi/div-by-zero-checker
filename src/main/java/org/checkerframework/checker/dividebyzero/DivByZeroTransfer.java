package org.checkerframework.checker.dividebyzero;

import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFAnalysis;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.ConditionalTransferResult;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

import javax.lang.model.element.AnnotationMirror;
import java.lang.annotation.Annotation;

import java.util.Arrays;
import java.util.Set;

import org.checkerframework.checker.dividebyzero.qual.*;

public class DivByZeroTransfer extends CFTransfer {

    enum Comparison {
        /** == */ EQ,
        /** != */ NE,
        /** <  */ LT,
        /** <= */ LE,
        /** >  */ GT,
        /** >= */ GE
    }

    enum BinaryOperator {
        /** + */ PLUS,
        /** - */ MINUS,
        /** * */ TIMES,
        /** / */ DIVIDE,
        /** % */ MOD
    }

    // All possible points in our lattice
    private final AnnotationMirror BOT = reflect(Bot.class);
    private final AnnotationMirror NEG = reflect(Negative.class);
    private final AnnotationMirror ZER = reflect(Zero.class);
    private final AnnotationMirror POS = reflect(Positive.class);
    private final AnnotationMirror NZE = reflect(NonZero.class);
    private final AnnotationMirror TOP = reflect(Top.class);

    // Transfer table used for DIVIDE and MOD operators. Defines (point, point) -> point
    private AnnotationMirror[][] DIVIDE_TRANSFER = new AnnotationMirror[][]{
            /** Bot   **/  {BOT, BOT, BOT, BOT, BOT, BOT},
            /** Neg   **/  {BOT, POS, TOP, NEG, NZE, TOP},
            /** Zero  **/  {BOT, ZER, TOP, ZER, ZER, TOP},
            /** Pos   **/  {BOT, NEG, TOP, POS, NZE, TOP},
            /** !Zero **/  {BOT, NZE, TOP, NZE, NZE, TOP},
            /** Top   **/  {BOT, TOP, TOP, TOP, TOP, TOP},
    };

    // Transfer table used for PLUS and MINUS operators. Defines (point, point) -> point
    private AnnotationMirror[][] PLUS_TRANSFER = new AnnotationMirror[][]{
            /** Bot   **/  {BOT, BOT, BOT, BOT, BOT, BOT},
            /** Neg   **/  {BOT, NEG, NEG, TOP, TOP, TOP},
            /** Zero  **/  {BOT, NEG, ZER, POS, NZE, TOP},
            /** Pos   **/  {BOT, TOP, ZER, POS, TOP, TOP},
            /** !Zero **/  {BOT, TOP, NZE, TOP, TOP, TOP},
            /** Top   **/  {BOT, TOP, TOP, TOP, TOP, TOP},
    };

    // Transfer table used for TIMES operators. Defines (point, point) -> point
    private AnnotationMirror[][] TIMES_TRANSFER = new AnnotationMirror[][]{
            /** Bot   **/  {BOT, BOT, BOT, BOT, BOT, BOT},
            /** Neg   **/  {BOT, POS, ZER, NEG, NZE, TOP},
            /** Zero  **/  {BOT, ZER, ZER, ZER, ZER, ZER},
            /** Pos   **/  {BOT, NEG, ZER, POS, NZE, TOP},
            /** !Zero **/  {BOT, NZE, ZER, NZE, NZE, TOP},
            /** Top   **/  {BOT, TOP, ZER, TOP, TOP, TOP},
    };

    // Refinement table used for REFINEMENT. Defines (op, point) -> point
    private AnnotationMirror[][] REFINEMENT = new AnnotationMirror[][]{
            /** EQ   **/  {BOT, NEG, ZER, POS, NZE, TOP},
            /** NE   **/  {TOP, TOP, NZE, TOP, ZER, BOT},
            /** LT   **/  {BOT, NEG, NEG, TOP, TOP, TOP},
            /** GT   **/  {BOT, TOP, POS, POS, TOP, TOP},
            /** LE   **/  {BOT, NEG, TOP, TOP, TOP, TOP},
            /** GE   **/  {BOT, TOP, TOP, POS, TOP, TOP},
    };

    // Transfer table used for TIMES operators. Defines (point, point) -> point
    private AnnotationMirror[][] GLB = new AnnotationMirror[][]{
            /** Bot   **/  {BOT, BOT, BOT, BOT, BOT, BOT},
            /** Neg   **/  {BOT, NEG, BOT, BOT, NEG, NEG},
            /** Zero  **/  {BOT, BOT, ZER, BOT, BOT, ZER},
            /** Pos   **/  {BOT, BOT, BOT, POS, POS, POS},
            /** !Zero **/  {BOT, NEG, BOT, POS, NZE, NZE},
            /** Top   **/  {BOT, NEG, ZER, POS, NZE, TOP},
    };

    // ========================================================================
    // Transfer functions to implement

    /**
     * Assuming that a simple comparison (lhs `op` rhs) returns true, this
     * function should refine what we know about the left-hand side (lhs). (The
     * input value "lhs" is always a legal return value, but not a very useful
     * one.)
     *
     * <p>For example, given the code
     * <pre>
     * if (y != 0) { x = 1 / y; }
     * </pre>
     * the comparison "y != 0" causes us to learn the fact that "y is not zero"
     * inside the body of the if-statement. This function would be called with
     * "NE", "top", and "zero", and should return "not zero" (or the appropriate
     * result for your lattice).
     *
     * <p>Note that the returned value should always be lower in the lattice
     * than the given point for lhs. The "glb" helper function below will
     * probably be useful here.
     *
     * @param operator   a comparison operator
     * @param lhs        the lattice point for the left-hand side of the comparison expression
     * @param rhs        the lattice point for the right-hand side of the comparison expression
     * @return a refined type for lhs
     */
    private AnnotationMirror refineLhsOfComparison(
            Comparison operator,
            AnnotationMirror lhs,
            AnnotationMirror rhs) {

        // Find what we know about an arbitrary LHS given operator and RHS
        int i = indexOf(operator);
        int j = indexOf(rhs);
        AnnotationMirror refinement = REFINEMENT[i][j];

        // We know what we used to know about LHS and refinement
//        return glb(lhs, refinement);
        i = indexOf(lhs);
        j = indexOf(refinement);
        return GLB[i][j];
    }

    /** Returns the index of the comparison operator as used in the refinement table **/
    private int indexOf(Comparison operator) {
        Comparison[] arr = {Comparison.EQ, Comparison.NE, Comparison.LT, Comparison.GT, Comparison.LE, Comparison.GE};
        return Arrays.asList(arr).indexOf(operator);
    }

    /**
     * For an arithmetic expression (lhs `op` rhs), compute the point in the
     * lattice for the result of evaluating the expression. ("Top" is always a
     * legal return value, but not a very useful one.)
     *
     * <p>For example,
     * <pre>x = 1 + 0</pre>
     * should cause us to conclude that "x is not zero".
     *
     * @param operator   a binary operator
     * @param lhs        the lattice point for the left-hand side of the expression
     * @param rhs        the lattice point for the right-hand side of the expression
     * @return the lattice point for the result of the expression
     */
    private AnnotationMirror arithmeticTransfer(
            BinaryOperator operator,
            AnnotationMirror lhs,
            AnnotationMirror rhs) {

        int i = indexOf(lhs);
        int j = indexOf(rhs);

        switch (operator) {
            case MOD:
            case DIVIDE:
                return DIVIDE_TRANSFER[i][j];
            case TIMES:
                return TIMES_TRANSFER[i][j];
            case PLUS:
                return PLUS_TRANSFER[i][j];
            case MINUS:
                j = indexOf(negate(rhs));  // a - b == a + (-b)
                return PLUS_TRANSFER[i][j];
        }
        return top();
    }

    /** Returns the index of the point in the lattice used by our lookup tables */
    private int indexOf(AnnotationMirror op) {
        AnnotationMirror[] arr = {BOT, NEG, ZER, POS, NZE, TOP};
        for (int i = 0; i < arr.length; i++) {
            if (equal(op, arr[i])) {
                return i;
            }
        }

        return -1;
    }

    /** Returns the negated version of the point in the lattice (e.g. -POS => NEG) **/
    private AnnotationMirror negate(AnnotationMirror op) {
        AnnotationMirror[] negated = {BOT, POS, ZER, NEG, NZE, TOP};
        return negated[indexOf(op)];
    }


    // ========================================================================
    // Useful helpers

    /** Get the top of the lattice */
    private AnnotationMirror top() {
        return analysis.getTypeFactory().getQualifierHierarchy().getTopAnnotations().iterator().next();
    }

    /** Get the bottom of the lattice */
    private AnnotationMirror bottom() {
        return analysis.getTypeFactory().getQualifierHierarchy().getBottomAnnotations().iterator().next();
    }

    /** Compute the least-upper-bound of two points in the lattice */
    private AnnotationMirror lub(AnnotationMirror x, AnnotationMirror y) {
        return analysis.getTypeFactory().getQualifierHierarchy().leastUpperBound(x, y);
    }

    /** Compute the greatest-lower-bound of two points in the lattice */
    private AnnotationMirror glb(AnnotationMirror x, AnnotationMirror y) {
        return analysis.getTypeFactory().getQualifierHierarchy().greatestLowerBound(x, y);
    }

    /** Convert a "Class" object (e.g. "Top.class") to a point in the lattice */
    private AnnotationMirror reflect(Class<? extends Annotation> qualifier) {
        return AnnotationBuilder.fromClass(
            analysis.getTypeFactory().getProcessingEnv().getElementUtils(),
            qualifier);
    }

    /** Determine whether two AnnotationMirrors are the same point in the lattice */
    private boolean equal(AnnotationMirror x, AnnotationMirror y) {
        return AnnotationUtils.areSame(x, y);
    }

    /** `x op y` == `y flip(op) x` */
    private Comparison flip(Comparison op) {
        switch (op) {
            case EQ: return Comparison.EQ;
            case NE: return Comparison.NE;
            case LT: return Comparison.GT;
            case LE: return Comparison.GE;
            case GT: return Comparison.LT;
            case GE: return Comparison.LE;
            default: throw new IllegalArgumentException(op.toString());
        }
    }

    /** `x op y` == `!(x negate(op) y)` */
    private Comparison negate(Comparison op) {
        switch (op) {
            case EQ: return Comparison.NE;
            case NE: return Comparison.EQ;
            case LT: return Comparison.GE;
            case LE: return Comparison.GT;
            case GT: return Comparison.LE;
            case GE: return Comparison.LT;
            default: throw new IllegalArgumentException(op.toString());
        }
    }

    // ========================================================================
    // Checker Framework plumbing

    public DivByZeroTransfer(CFAnalysis analysis) {
        super(analysis);
    }

    private TransferResult<CFValue, CFStore> implementComparison(Comparison op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
        QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
        AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

        if (l == null || r == null) {
            // this can happen for generic types
            return out;
        }

        CFStore thenStore = out.getThenStore().copy();
        CFStore elseStore = out.getElseStore().copy();

        thenStore.insertValue(
                JavaExpression.fromNode(n.getLeftOperand()),
            refineLhsOfComparison(op, l, r));

        thenStore.insertValue(
            JavaExpression.fromNode(n.getRightOperand()),
            refineLhsOfComparison(flip(op), r, l));

        elseStore.insertValue(
            JavaExpression.fromNode(n.getLeftOperand()),
            refineLhsOfComparison(negate(op), l, r));

        elseStore.insertValue(
            JavaExpression.fromNode(n.getRightOperand()),
            refineLhsOfComparison(flip(negate(op)), r, l));

        return new ConditionalTransferResult<>(out.getResultValue(), thenStore, elseStore);
    }

    private TransferResult<CFValue, CFStore> implementOperator(BinaryOperator op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
        QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        AnnotationMirror l = findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
        AnnotationMirror r = findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

        if (l == null || r == null) {
            // this can happen for generic types
            return out;
        }

        AnnotationMirror res = arithmeticTransfer(op, l, r);
        CFValue newResultValue = analysis.createSingleAnnotationValue(res, out.getResultValue().getUnderlyingType());
        return new RegularTransferResult<>(newResultValue, out.getRegularStore());
    }

    @Override
    public TransferResult<CFValue, CFStore> visitEqualTo(EqualToNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.EQ, n, super.visitEqualTo(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNotEqual(NotEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.NE, n, super.visitNotEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThan(GreaterThanNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.GT, n, super.visitGreaterThan(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitGreaterThanOrEqual(GreaterThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.GE, n, super.visitGreaterThanOrEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThan(LessThanNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.LT, n, super.visitLessThan(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitLessThanOrEqual(LessThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
        return implementComparison(Comparison.LE, n, super.visitLessThanOrEqual(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitIntegerDivision(IntegerDivisionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.DIVIDE, n, super.visitIntegerDivision(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitIntegerRemainder(IntegerRemainderNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MOD, n, super.visitIntegerRemainder(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitFloatingDivision(FloatingDivisionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.DIVIDE, n, super.visitFloatingDivision(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitFloatingRemainder(FloatingRemainderNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MOD, n, super.visitFloatingRemainder(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalMultiplication(NumericalMultiplicationNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.TIMES, n, super.visitNumericalMultiplication(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalAddition(NumericalAdditionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.PLUS, n, super.visitNumericalAddition(n, p));
    }

    @Override
    public TransferResult<CFValue, CFStore> visitNumericalSubtraction(NumericalSubtractionNode n, TransferInput<CFValue, CFStore> p) {
        return implementOperator(BinaryOperator.MINUS, n, super.visitNumericalSubtraction(n, p));
    }

    private static AnnotationMirror findAnnotation(
            Set<AnnotationMirror> set, QualifierHierarchy hierarchy) {
        if (set.size() == 0) {
            return null;
        }
        Set<? extends AnnotationMirror> tops = hierarchy.getTopAnnotations();
        return hierarchy.findAnnotationInSameHierarchy(set, tops.iterator().next());
    }

}
