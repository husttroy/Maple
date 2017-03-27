package edu.ucla.cs.parse;

import java.util.ArrayList;
import java.util.HashMap;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.MethodDeclaration;

import edu.ucla.cs.model.APISeqItem;

public class MethodVisitor extends ASTVisitor{
	public HashMap<String, ArrayList<APISeqItem>> seqs = new HashMap<String, ArrayList<APISeqItem>>();
	
	public boolean visit(MethodDeclaration node) {
		String method = node.getName().toString();
		
		APICallVisitor cv = new APICallVisitor();
		node.accept(cv);
		seqs.put(method, cv.seq);
		
		return false;
	}
}
