package edu.ucla.cs.parse;

import java.util.ArrayList;
import java.util.HashSet;

import org.apache.commons.lang3.StringEscapeUtils;
import org.eclipse.jdt.core.dom.CompilationUnit;

import edu.ucla.cs.model.APISeqItem;

public class PartialProgramAnalyzer {
	CompilationUnit cu;
	
	public PartialProgramAnalyzer(String snippet) throws Exception {
		PartialProgramParser parser = new PartialProgramParser();
		// unescape html special characters, e.g., &amp;&amp; will become &&
		String code = StringEscapeUtils.unescapeHtml4(snippet);
		this.cu = parser.getCompilationUnitFromString(code);
		if(this.cu == null) {
			throw new Exception("Partial Program Parse Error!");
		}
	}
	
	public ArrayList<APISeqItem> retrieveAPICallSequences() {
		if (this.cu == null) {
			return null;
		}
		
		APICallVisitor visitor = new APICallVisitor();
		this.cu.accept(visitor);
		return visitor.seq;
	}
	
	public HashSet<String> retrieveTypes() {
		if (this.cu == null) {
			return null;
		}
		
		APITypeVisitor visitor = new APITypeVisitor();
		this.cu.accept(visitor);
		return visitor.types;
	}
}
