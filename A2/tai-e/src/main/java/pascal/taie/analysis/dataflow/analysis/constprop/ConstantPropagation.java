/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import static pascal.taie.ir.exp.ArithmeticExp.Op.DIV;
import static pascal.taie.ir.exp.ArithmeticExp.Op.REM;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // initialize cfg's CPFact
        var fact = newInitialFact();
        // ???
        for (var variable : cfg.getIR().getParams()) {
            if (canHoldInt(variable)) {
                // fill fact but idn what getIR and getParams is
                fact.update(variable, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // create a new CPFact
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var key: fact.keySet()) {
            // merge fact into target, but shouldn't it be into fact instead of current order
            target.update(key, meetValue(fact.get(key), target.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // chk constant
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) {
                // if the same, merge them
                return Value.makeConstant(v1.getConstant());
            } else {
                // else unknown state, not constant
                return Value.getNAC();
            }
        } else if (v1.isNAC() || v2.isNAC()) {
            // nac + anything -> nac
            return Value.getNAC();
            // if const exists and there is no nac, assign the const
        } else if (v1.isConstant() && v2.isUndef()) {
            return Value.makeConstant(v1.getConstant());
        } else if (v1.isUndef() && v2.isConstant()) {
            return Value.makeConstant(v2.getConstant());
        }
        // finally uninitialized values
        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        var changed = false;
        // in case of poisoned out
        out.copyFrom(in);
        if (stmt instanceof DefinitionStmt defStmt) {
            // get lv -- key
            var lv = defStmt.getLValue();
            if (lv instanceof Var variable && canHoldInt(variable)) {
                var temp = in.copy();
                // get new value
                var newVal = evaluate(defStmt.getRValue(), in);
                // update out
                temp.update(variable, newVal);

                // merge out and in
                if (in.get(variable) != newVal) {
                    out.copyFrom(temp);
                    changed = true;
                }
            }
        }

        return changed;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    // nothing to say
    public static Value evaluate(Exp exp, CPFact in) {
        // available expression --- IntLit, ArithmeticExp, BinExp, BitwiseExp, CondExp, Var, ShiftExp
        if (exp instanceof IntLiteral lit) {
            var constant = lit.getValue();
            return Value.makeConstant(constant);
        }

        if (exp instanceof Var variable) {
            return in.get(variable);
        }

        // binary expression --- + - * / % bitOp rOp
        if (exp instanceof BinaryExp bin) {
            var var1 = evaluate(bin.getOperand1(), in);
            var var2 = evaluate(bin.getOperand2(), in);
            var op = bin.getOperator();

            // div zero / rem zero
            if (var2.isConstant() && (op.equals(DIV) || op.equals(REM)) && var2.getConstant() == 0) {
                return Value.getUndef();
            }

            var result = Value.getUndef();
            if (var1.isConstant() && var2.isConstant()) {
                var c1 = var1.getConstant();
                var c2 = var2.getConstant();

                // since java17 forbids some operations concerning switch (op)
                if (exp instanceof ArithmeticExp ariExp) {
                    result = switch (ariExp.getOperator()) {
                        case ADD -> Value.makeConstant(c1 + c2);
                        case SUB -> Value.makeConstant(c1 - c2);
                        case MUL -> Value.makeConstant(c1 * c2);
                        case DIV -> Value.makeConstant(c1 / c2);
                        case REM -> Value.makeConstant(c1 % c2);
                    };
                }

                if (exp instanceof BitwiseExp bwExp) {
                    result = switch (bwExp.getOperator()) {
                        case OR -> Value.makeConstant(c1 | c2);
                        case AND -> Value.makeConstant(c1 & c2);
                        case XOR -> Value.makeConstant(c1 ^ c2);
                    };
                }

                if (exp instanceof ConditionExp conExp) {
                    result = switch (conExp.getOperator()) {
                        case EQ -> Value.makeConstant(c1 == c2 ? 1 : 0);
                        case NE -> Value.makeConstant(c1 != c2 ? 1 : 0);
                        case GT -> Value.makeConstant(c1 > c2 ? 1 : 0);
                        case LT -> Value.makeConstant(c1 < c2 ? 1 : 0);
                        case GE -> Value.makeConstant(c1 >= c2 ? 1 : 0);
                        case LE -> Value.makeConstant(c1 <= c2 ? 1 : 0);
                    };
                }

                if (exp instanceof ShiftExp shExp) {
                    result = switch (shExp.getOperator()) {
                        case SHL -> Value.makeConstant(c1<<c2);
                        case SHR -> Value.makeConstant(c1>>c2);
                        case USHR -> Value.makeConstant(c1>>>c2);
                    };
                }
            } else if (var1.isNAC() || var2.isNAC()) {
                result = Value.getNAC();
            }

            return result;
        }

        return Value.getNAC();
    }
}

