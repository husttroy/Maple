package edu.ucla.cs.verify.threshold;

import java.util.ArrayList;

import edu.ucla.cs.mine.PreconditionVerifier;
import edu.ucla.cs.mine.SequencePatternVerifier;
import edu.ucla.cs.utils.FileUtils;

public class FileInputStream {
	public static void main(String[] args) {
		String raw_output = "/home/troy/research/BOA/Maple/example/FileInputStream.new/large-sequence.txt";
		String seq_output = "/home/troy/research/BOA/Maple/example/FileInputStream.new/large-output.txt";
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("new FileInputStream(1)");
		int size = FileUtils.countLines(seq_output);
				
		// verify sequence
		pattern.add(0, "TRY {");
		pattern.add("}");
		pattern.add("CATCH {");
		pattern.add("}");
		SequencePatternVerifier pv = new SequencePatternVerifier(pattern);
		pv.verify(seq_output);
		double r1 = ((double) pv.support.size()) / size;
		System.out.println("sequence threshold: " + r1);
		pattern.remove(0);
		pattern.remove(1);
		pattern.remove(1);
		pattern.remove(1);
		 
		// verify precondition
		PreconditionVerifier pv2 = new PreconditionVerifier(raw_output, seq_output, pattern);
		int count = pv2.verify("new FileInputStream(1)", "!arg0.exists()");
		double r2 = ((double) count) / size;
		System.out.println("precondition threshold: " + r2);			
	} 
}
