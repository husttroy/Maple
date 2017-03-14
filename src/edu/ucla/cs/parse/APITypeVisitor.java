package edu.ucla.cs.parse;

import java.util.HashSet;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ParameterizedType;
import org.eclipse.jdt.core.dom.QualifiedType;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.VariableDeclarationExpression;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;

public class APITypeVisitor extends ASTVisitor{
	public HashSet<String> types;
	
	public APITypeVisitor() {
		types = new HashSet<String>();
	}
	
	@Override
	public boolean visit(SingleVariableDeclaration node) {
		Type t = node.getType();
		getType(t);
		return false;
	}
	
	@Override
	public boolean visit(FieldDeclaration node){
		Type t = node.getType();
		getType(t);
		return false;
	}
	
	@Override
	public boolean visit(VariableDeclarationStatement node){
		Type t = node.getType();
		getType(t);
		return false;
	}
	
	@Override
	public boolean visit(VariableDeclarationExpression node){
		Type t = node.getType();
		getType(t);
		return false;
	}
	
	private void getType(Type node) {
		String type = node.toString();
		if(node.isNameQualifiedType()) {
			types.add(type);
			QualifiedType qtype = (QualifiedType)node;
			types.add(qtype.getName().toString());
		} else if (node.isParameterizedType()) {
			types.add(type);
			ParameterizedType ptype = (ParameterizedType)node;
			types.add(ptype.getType().toString());
			List<Type> params = ptype.typeArguments();
			for(Type param : params) {
				getType(param);
			}
		} else {
			types.add(type);
		}
	}
}
