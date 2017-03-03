package edu.ucla.cs.parse;

import java.io.IOException;
import java.util.ArrayList;

import org.eclipse.jdt.core.dom.CompilationUnit;

import edu.ucla.cs.model.APISeqItem;

public class PartialProgramAnalyzer {
	
	public ArrayList<APISeqItem> analyze(String snippet) {
		PartialProgramParser parser = new PartialProgramParser();
		CompilationUnit cu;
		try {
			cu = parser.getCompilationUnitFromString(snippet);
		} catch (NullPointerException | ClassNotFoundException | IOException e) {
			return null;
		}
		
		return retrieveAPICallSequences(cu);
	}
	
	private ArrayList<APISeqItem> retrieveAPICallSequences(CompilationUnit cu) {
		APICallVisitor visitor = new APICallVisitor();
		cu.accept(visitor);
		return visitor.seq;
	}
}
