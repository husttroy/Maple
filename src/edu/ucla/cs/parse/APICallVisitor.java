package edu.ucla.cs.parse;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.CatchClause;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.EnhancedForStatement;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.TryStatement;
import org.eclipse.jdt.core.dom.WhileStatement;

import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlContruct;

public class APICallVisitor extends ASTVisitor {
	public ArrayList<APISeqItem> seq = new ArrayList<APISeqItem>();
	public String condition = "true";

	// visit method calls including regular method calls, calls to super
	// methods, and class instantiation
	public boolean visit(MethodInvocation node) {
		// System.out.println(node.getName().toString());

		// visit receiver first just in case if the receiver is also a method
		// call
		Expression expr = node.getExpression();
		String receiver = null;
		if (expr != null) {
			receiver = expr.toString();
			expr.accept(this);
		}

		// visit arguments first to chain up any method calls in the argument
		// list
		List<Expression> args = node.arguments();
		ArrayList<String> arguments = new ArrayList<String>();
		for (Expression arg : args) {
			arguments.add(arg.toString());
			arg.accept(this);
		}

		seq.add(new APICall(node.getName().toString(), condition, receiver, arguments));

		return false;
	}

	public boolean visit(SuperMethodInvocation node) {
		// System.out.println("super." + node.getName().toString());

		// visit arguments first to chain up any method calls in the argument
		// list
		List<Expression> args = node.arguments();
		ArrayList<String> arguments = new ArrayList<String>();
		for (Expression arg : args) {
			arguments.add(arg.toString());
			arg.accept(this);
		}

		seq.add(new APICall("super." + node.getName().toString(), condition, null, arguments));

		return false;
	}

	public boolean visit(ClassInstanceCreation node) {
		// System.out.println("new " + node.getType().toString());

		// visit arguments first to chain up any method calls in the argument
		// list
		List<Expression> args = node.arguments();
		ArrayList<String> arguments = new ArrayList<String>();
		for (Expression arg : args) {
			arguments.add(arg.toString());
			arg.accept(this);
		}

		seq.add(new APICall("new " + node.getType().toString(), condition, null, arguments));

		return false;
	}

	// visit control-flow structures
	public boolean visit(TryStatement node) {
		// System.out.println("Try");
		seq.add(ControlContruct.TRY);

		node.getBody().accept(this);
		this.seq.add(ControlContruct.END_BLOCK);

		List<CatchClause> catches = node.catchClauses();
		for (CatchClause c : catches) {
			c.accept(this);
		}

		Block fblock = node.getFinally();
		if (fblock != null) {
			// System.out.println("Finally");
			seq.add(ControlContruct.FINALLY);
			fblock.accept(this);
			seq.add(ControlContruct.END_BLOCK);
		}

		return false;
	}

	public boolean visit(CatchClause node) {
		// System.out.println("catch");
		seq.add(ControlContruct.CATCH);
		return true;
	}

	public void endVisit(CatchClause node) {
		this.seq.add(ControlContruct.END_BLOCK);
	}

	public boolean visit(IfStatement node) {
		// System.out.println("If");
		seq.add(ControlContruct.IF);

		String oldCond = condition;
		Expression expr = node.getExpression();
		// System.out.println(expr.toString());
		if (oldCond.equals("true")) {
			condition = expr.toString();
		} else {
			condition = oldCond + " && " + expr.toString();
		}

		Statement thenStmt = node.getThenStatement();
		thenStmt.accept(this);
		this.seq.add(ControlContruct.END_BLOCK);

		Statement elseStmt = node.getElseStatement();
		if (elseStmt != null) {
			// System.out.println("else");
			if (oldCond.equals("true")) {
				condition = "!(" + expr.toString() + ")";
			} else {
				condition = oldCond + " && !(" + expr.toString() + ")";
			}

			seq.add(ControlContruct.ELSE);
			elseStmt.accept(this);
			this.seq.add(ControlContruct.END_BLOCK);
		}

		condition = oldCond;

		return false;
	}

	public boolean visit(ForStatement node) {
		// System.out.println("Loop");
		seq.add(ControlContruct.LOOP);

		String oldCond = condition;
		Expression expr = node.getExpression();
		if (expr != null) {
			if (oldCond.equals("true")) {
				condition = expr.toString();
			} else {
				condition = oldCond + " && " + expr.toString();
			}
		}

		Statement stmt = node.getBody();
		stmt.accept(this);

		condition = oldCond;

		return false;
	}

	public void endVisit(ForStatement node) {
		this.seq.add(ControlContruct.END_BLOCK);
	}

	public boolean visit(EnhancedForStatement node) {
		// System.out.println("Loop");
		seq.add(ControlContruct.LOOP);

		Expression expr = node.getExpression();
		String oldCond = condition;
		if (oldCond.equals("true")) {
			condition = expr.toString() + ".size() > 0";
		} else {
			condition = oldCond + " && " + expr.toString() + ".size() > 0";
		}

		Statement stmt = node.getBody();
		stmt.accept(this);

		condition = oldCond;

		return false;
	}

	public void endVisit(EnhancedForStatement node) {
		this.seq.add(ControlContruct.END_BLOCK);
	}

	public boolean visit(WhileStatement node) {
		// System.out.println("Loop");
		seq.add(ControlContruct.LOOP);

		Expression expr = node.getExpression();
		String oldCond = condition;
		if (expr != null) {
			if (oldCond.equals("true")) {
				condition = expr.toString();
			} else {
				condition = oldCond + " && " + expr.toString();
			}
		}

		Statement stmt = node.getBody();
		stmt.accept(this);

		condition = oldCond;

		return false;
	}

	public void endVisit(WhileStatement node) {
		this.seq.add(ControlContruct.END_BLOCK);
	}
}
