package org.checkerframework.checker.dividebyzero;

import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;

import javax.lang.model.type.TypeKind;
import java.lang.annotation.Annotation;
import com.sun.source.tree.*;

import java.util.Set;
import java.util.EnumSet;

import org.checkerframework.checker.dividebyzero.qual.*;

public class DivByZeroVisitor extends BaseTypeVisitor<DivByZeroAnnotatedTypeFactory> {

    /** Set of operators we care about */
    private static final Set<Tree.Kind> DIVISION_OPERATORS = EnumSet.of(
        /* x /  y */ Tree.Kind.DIVIDE,
        /* x /= y */ Tree.Kind.DIVIDE_ASSIGNMENT,
        /* x %  y */ Tree.Kind.REMAINDER,
        /* x %= y */ Tree.Kind.REMAINDER_ASSIGNMENT);

    private static final Set<TypeKind> INT_TYPES = EnumSet.of(
            TypeKind.INT,
            TypeKind.LONG);

    /**
     * Determine whether to report an error at the given binary AST node.
     * The error text is defined in the messages.properties file.
     * @param node the AST node to inspect
     * @return true if an error should be reported, false otherwise
     */
    private boolean errorAt(BinaryTree node) {

        // Is this an operator that can have divide by zero errors?
        Tree.Kind operator = node.getKind();
        if (!DIVISION_OPERATORS.contains(operator)) {
            return false;
        }

        // Can't have a divide by zero unless both sides are INT_TYPES
        // E.g. (0.0 / 0)  =>  (0.0 / 0.0)  =>  Double.NaN (?)
        ExpressionTree lhs = node.getLeftOperand();
        ExpressionTree rhs = node.getRightOperand();
        if (!isInt(lhs) || !isInt(rhs)) {
            return false;
        }

        System.out.println(node + ";" + hasAnnotation(rhs, Zero.class) + ";" + hasAnnotation(rhs, Top.class));
        return hasAnnotation(rhs, Zero.class) || hasAnnotation(rhs, Top.class);
    }

    /**
     * Determine whether to report an error at the given compound assignment
     * AST node. The error text is defined in the messages.properties file.
     * @param node the AST node to inspect
     * @return true if an error should be reported, false otherwise
     */
    private boolean errorAt(CompoundAssignmentTree node) {
        // A CompoundAssignmentTree represents any binary operator combined with an assignment,
        // such as "x += 10".

        // Is this an operator that can have divide by zero errors?
        Tree.Kind operator = node.getKind();
        if (!DIVISION_OPERATORS.contains(operator)) {
            return false;
        }

        // Can't have a divide unless rhs is an INT_TYPES
        ExpressionTree exp = node.getExpression();
        if (!isInt(exp)) {
            return false;
        }

        return hasAnnotation(exp, Zero.class) || hasAnnotation(exp, Top.class);
    }

    // ========================================================================
    // Useful helpers

    private boolean isInt(Tree node) {
        return INT_TYPES.contains(atypeFactory.getAnnotatedType(node).getKind());
    }

    private boolean hasAnnotation(Tree node, Class<? extends Annotation> c) {
        return atypeFactory.getAnnotatedType(node).hasAnnotation(c);
    }

    // ========================================================================
    // Checker Framework plumbing

    public DivByZeroVisitor(BaseTypeChecker c) {
        super(c);
    }

    @Override
    public Void visitBinary(BinaryTree node, Void p) {
        if (isInt(node)) {
            if (errorAt(node)) {
                checker.reportError(node, "divide.by.zero");
//                System.out.println("ERROR: " + node);
            }
        }
        return super.visitBinary(node, p);
    }

    @Override
    public Void visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
        if (isInt(node.getExpression())) {
            if (errorAt(node)) {
                checker.reportError(node, "divide.by.zero");
            }
        }
        return super.visitCompoundAssignment(node, p);
    }

}
