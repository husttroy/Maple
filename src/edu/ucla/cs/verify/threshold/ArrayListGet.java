package edu.ucla.cs.verify.threshold;

import java.util.ArrayList;

import edu.ucla.cs.mine.PreconditionVerifier;
import edu.ucla.cs.mine.SequencePatternVerifier;
import edu.ucla.cs.utils.FileUtils;

public class ArrayListGet {
	public static void main(String[] args) {
		String raw_output = "/home/troy/research/BOA/Maple/example/ArrayList.get/large-sequence.txt";
		String seq_output = "/home/troy/research/BOA/Maple/example/ArrayList.get/large-output.txt";
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("get(1)");
		int size = FileUtils.countLines(seq_output);
				
		// verify sequence
		pattern.add(0, "add(1)");
		SequencePatternVerifier pv = new SequencePatternVerifier(pattern);
		pv.verify(seq_output);
		double r1 = ((double) pv.support.size()) / size;
		System.out.println("sequence threshold: " + r1);
		pattern.remove(0);
		 
		// verify precondition
		PreconditionVerifier pv2 = new PreconditionVerifier(raw_output, seq_output, pattern);
		int count = pv2.verify("get(1)", "arg0 < rcv.size()");
		double r2 = ((double) count) / size;
		System.out.println("precondition threshold: " + r2);		
	}
}
