package edu.ucla.cs.mine;

import java.util.ArrayList;

public class FrequentSequenceMiner extends PatternMiner {

	public FrequentSequenceMiner(String script_path, String seqs_path,
			int min_support, ArrayList<String> filter) {
		super(script_path, seqs_path, min_support, filter);
	}

	@Override
	protected void process(String input) {
		String[] ss = input.split(System.lineSeparator());
		
		for(String s : ss) {
			// process each pattern detected by the frequent item miner
			if(s.startsWith("(") && s.endsWith(")")) {
				int support = Integer.valueOf(s.substring(s.lastIndexOf(", ") + 2, s.lastIndexOf(")")));
				String sequence = s.substring(s.indexOf("(") + 1, s.lastIndexOf(", "));
				
				ArrayList<String> pattern = new ArrayList<String>();
				sequence = sequence.substring(sequence.indexOf("(") + 1, sequence.lastIndexOf(")"));
				String[] arr = sequence.split(", ");
				for(String api : arr){
					// strip ' '
					api = api.substring(1, api.length()-1);
					pattern.add(api);
				}
				
				this.patterns.put(pattern, support);
			}
		}
	}

	@Override
	protected void filter() {
		ArrayList<ArrayList<String>> remove = new ArrayList<ArrayList<String>>();
		
		// check whether each pattern is satisfiable
		for(ArrayList<String> pattern : this.patterns.keySet()) {
			if(!isSubsequence(pattern, this.query) || !isBalanced(pattern) || !isComplete(pattern)){
				remove.add(pattern);
			}
		}
		
		// remove unsatisfied patterns
		for(ArrayList<String> pattern : remove) {
			this.patterns.remove(pattern);
		}
	}
	
	/**
	 * Check whether the second sequence is a subseqeunce of the first one.
	 * 
	 * @param seq1
	 * @param seq2
	 * @return
	 */
	private boolean isSubsequence(ArrayList<String> seq1, ArrayList<String> seq2){
		ArrayList<String> seq2_copy = new ArrayList<String>(seq2);
		for(String s1 : seq1) {
			if (seq2_copy.isEmpty()) return true;
			String s2 = seq2_copy.get(0);
			if(s1.equals(s2)) {
				seq2_copy.remove(0);
			}
		}
		
		return seq2_copy.isEmpty();
	}
	
	public static void main(String[] args){
		ArrayList<String> query = new ArrayList<String>();
		query.add("createNewFile");
		PatternMiner pm = new FrequentSequenceMiner("/home/troy/research/BOA/Slicer/mining/freq_seq.py", 
				"/home/troy/research/BOA/Slicer/example/output.txt",
				40,
				query);
		pm.mine();
		for(ArrayList<String> pattern : pm.patterns.keySet()) {
			System.out.println(pattern + ":" + pm.patterns.get(pattern));
		}
	}
}
