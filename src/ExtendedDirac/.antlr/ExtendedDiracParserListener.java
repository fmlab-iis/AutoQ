// Generated from /home/alan23273850/AutoQ/src/ExtendedDirac/ExtendedDiracParser.g4 by ANTLR 4.13.1
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link ExtendedDiracParser}.
 */
public interface ExtendedDiracParserListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link ExtendedDiracParser#expr}.
	 * @param ctx the parse tree
	 */
	void enterExpr(ExtendedDiracParser.ExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExtendedDiracParser#expr}.
	 * @param ctx the parse tree
	 */
	void exitExpr(ExtendedDiracParser.ExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExtendedDiracParser#tset}.
	 * @param ctx the parse tree
	 */
	void enterTset(ExtendedDiracParser.TsetContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExtendedDiracParser#tset}.
	 * @param ctx the parse tree
	 */
	void exitTset(ExtendedDiracParser.TsetContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExtendedDiracParser#set}.
	 * @param ctx the parse tree
	 */
	void enterSet(ExtendedDiracParser.SetContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExtendedDiracParser#set}.
	 * @param ctx the parse tree
	 */
	void exitSet(ExtendedDiracParser.SetContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExtendedDiracParser#diracs}.
	 * @param ctx the parse tree
	 */
	void enterDiracs(ExtendedDiracParser.DiracsContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExtendedDiracParser#diracs}.
	 * @param ctx the parse tree
	 */
	void exitDiracs(ExtendedDiracParser.DiracsContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExtendedDiracParser#dirac}.
	 * @param ctx the parse tree
	 */
	void enterDirac(ExtendedDiracParser.DiracContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExtendedDiracParser#dirac}.
	 * @param ctx the parse tree
	 */
	void exitDirac(ExtendedDiracParser.DiracContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExtendedDiracParser#term}.
	 * @param ctx the parse tree
	 */
	void enterTerm(ExtendedDiracParser.TermContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExtendedDiracParser#term}.
	 * @param ctx the parse tree
	 */
	void exitTerm(ExtendedDiracParser.TermContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExtendedDiracParser#varcons}.
	 * @param ctx the parse tree
	 */
	void enterVarcons(ExtendedDiracParser.VarconsContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExtendedDiracParser#varcons}.
	 * @param ctx the parse tree
	 */
	void exitVarcons(ExtendedDiracParser.VarconsContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExtendedDiracParser#varcon}.
	 * @param ctx the parse tree
	 */
	void enterVarcon(ExtendedDiracParser.VarconContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExtendedDiracParser#varcon}.
	 * @param ctx the parse tree
	 */
	void exitVarcon(ExtendedDiracParser.VarconContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExtendedDiracParser#ineq}.
	 * @param ctx the parse tree
	 */
	void enterIneq(ExtendedDiracParser.IneqContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExtendedDiracParser#ineq}.
	 * @param ctx the parse tree
	 */
	void exitIneq(ExtendedDiracParser.IneqContext ctx);
}