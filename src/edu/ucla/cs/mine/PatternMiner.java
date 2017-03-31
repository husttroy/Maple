package edu.ucla.cs.mine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.ControlConstruct;

public class PatternMiner {
	public static HashMap<ArrayList<APISeqItem>, Integer> mine(String raw_output, String sequence, HashSet<HashSet<String>> apis, double support, int size) {
		int threshold = (int) (support * size);
		SequencePatternMiner pm = new FrequentSequenceMiner(
				"/home/troy/research/BOA/Maple/mining/freq_seq.py",
				sequence,
				threshold, apis);
		HashMap<ArrayList<String>, Integer>  patterns = pm.mine();
		HashMap<ArrayList<APISeqItem>, Integer> composed_patterns = new HashMap<ArrayList<APISeqItem>, Integer>();
		for(ArrayList<String> seq_pattern : patterns.keySet()) {
			PredicatePatternMiner pm2 = new TraditionalPredicateMiner(seq_pattern, raw_output, sequence);
			pm2.process();
			int seq_support = patterns.get(seq_pattern);
			int threshold2 = (int) (support * seq_support);
			HashMap<String, HashMap<String, Integer>> predicate_patterns = pm2.find_the_most_common_predicate(threshold2);
			HashMap<ArrayList<APISeqItem>, Integer> cp = compose(seq_pattern, seq_support, predicate_patterns, size);
			if(cp != null) {
				composed_patterns.putAll(cp);
			}
		}
		
		return composed_patterns;
	}
	
	private static HashMap<ArrayList<APISeqItem>, Integer> compose(
			ArrayList<String> seq_pattern,
			int seq_support,
			HashMap<String, HashMap<String, Integer>> pred_patterns, int size) {
		HashMap<ArrayList<APISeqItem>, Integer> composed_patterns = new HashMap<ArrayList<APISeqItem>, Integer>();
		
		for(String api : seq_pattern) {
			if(api.equals("}")) {
				if(composed_patterns.isEmpty()) {
					// this is the first element in the sequence pattern
					ArrayList<APISeqItem> s = new ArrayList<APISeqItem>();
					s.add(ControlConstruct.END_BLOCK);
					composed_patterns.put(s, seq_support);
				} else {
					for(ArrayList<APISeqItem> s : composed_patterns.keySet()) {
						s.add(ControlConstruct.END_BLOCK);
					}
				}
			} else if (api.equals("TRY {")) {
				if(composed_patterns.isEmpty()) {
					// this is the first element in the sequence pattern
					ArrayList<APISeqItem> s = new ArrayList<APISeqItem>();
					s.add(ControlConstruct.TRY);
					composed_patterns.put(s, seq_support);
				} else {
					for(ArrayList<APISeqItem> s : composed_patterns.keySet()) {
						s.add(ControlConstruct.TRY);
					}
				}
			} else if (api.equals("IF {")) {
				if(composed_patterns.isEmpty()) {
					// this is the first element in the sequence pattern
					ArrayList<APISeqItem> s = new ArrayList<APISeqItem>();
					s.add(ControlConstruct.IF);
					composed_patterns.put(s, seq_support);
				} else {
					for(ArrayList<APISeqItem> s : composed_patterns.keySet()) {
						s.add(ControlConstruct.IF);
					}
				}
			} else if (api.equals("LOOP {")) {
				if(composed_patterns.isEmpty()) {
					// this is the first element in the sequence pattern
					ArrayList<APISeqItem> s = new ArrayList<APISeqItem>();
					s.add(ControlConstruct.LOOP);
					composed_patterns.put(s, seq_support);
				} else {
					for(ArrayList<APISeqItem> s : composed_patterns.keySet()) {
						s.add(ControlConstruct.LOOP);
					}
				}
			} else if (api.equals("CATCH {")) {
				if(composed_patterns.isEmpty()) {
					// this is the first element in the sequence pattern
					ArrayList<APISeqItem> s = new ArrayList<APISeqItem>();
					s.add(ControlConstruct.CATCH);
					composed_patterns.put(s, seq_support);
				} else {
					for(ArrayList<APISeqItem> s : composed_patterns.keySet()) {
						s.add(ControlConstruct.CATCH);
					}
				}
			} else if (api.equals("FINALLY {")) {
				if(composed_patterns.isEmpty()) {
					// this is the first element in the sequence pattern
					ArrayList<APISeqItem> s = new ArrayList<APISeqItem>();
					s.add(ControlConstruct.FINALLY);
					composed_patterns.put(s, seq_support);
				} else {
					for(ArrayList<APISeqItem> s : composed_patterns.keySet()) {
						s.add(ControlConstruct.FINALLY);
					}
				}
			} else if (api.equals("ELSE {")){
				if(composed_patterns.isEmpty()) {
					// this is the first element in the sequence pattern
					ArrayList<APISeqItem> s = new ArrayList<APISeqItem>();
					s.add(ControlConstruct.ELSE);
					composed_patterns.put(s, seq_support);
				} else {
					for(ArrayList<APISeqItem> s : composed_patterns.keySet()) {
						s.add(ControlConstruct.ELSE);
					}
				}
			} else {
				HashMap<String, Integer> conditions;
				if(pred_patterns.containsKey(api)) {
					conditions = pred_patterns.get(api);
				} else {
					conditions = new HashMap<String, Integer>();
					conditions.put("true", seq_support);
				}
				
				// split the name and the number of arguments of the API
				String tmp = api.substring(api.indexOf('(') + 1, api.indexOf(')'));
				int args = Integer.parseInt(tmp);
				String name = api.substring(0, api.indexOf('('));
				
				if(composed_patterns.isEmpty()) {
					// this is the first element in the sequence pattern
					for(String condition : conditions.keySet()) {
						// initialize
						ArrayList<APISeqItem> s = new ArrayList<APISeqItem>();
						s.add(new APICall(name, condition, args));
						composed_patterns.put(s, conditions.get(condition));
					}
				} else {
					HashMap<ArrayList<APISeqItem>, Integer> newAll = new HashMap<ArrayList<APISeqItem>, Integer>();
					boolean flag = isConditional(seq_pattern, api);
					// propagate the new API with all possible predicates to each record in the map
					for(Map.Entry<ArrayList<APISeqItem>, Integer> entry : composed_patterns.entrySet()) {
						ArrayList<APISeqItem> s = entry.getKey();
						int support1 = entry.getValue();
						
						if(conditions.size() > 1 && conditions.containsKey("true")) {
							// we prefer conditions that are not true above the threshold
							conditions.remove("true");
						} else if (conditions.size() == 1 && conditions.containsKey("true") && flag) {
							// ignore this pattern
							return null;
						}
						
						for(String condition : conditions.keySet()) {
//							int support2 = (int) (conditions.get(condition) * ((double) support1) / size);
							int support2 = conditions.get(condition);
							int value = Math.min(support1, support2);
							ArrayList<APISeqItem> newS = new ArrayList<APISeqItem>();
							newS.addAll(s);
							newS.add(new APICall(name, condition, args));
							newAll.put(newS, value);
						}
					}
					composed_patterns = newAll;
				}
			}
		}
		
		return composed_patterns;
	}
	
	
	/**
	 * 
	 * check whether this API is wrapped by a conditional statement like if-else or loop
	 * 
	 * @param seq_pattern
	 * @param api
	 * @return
	 */
	private static boolean isConditional(ArrayList<String> seq_pattern, String api) {
		int count = 0;
		for(String s : seq_pattern) {
			if(api.equals(s)) {
				break;
			} else if (s.equals("IF {") || s.equals("LOOP {")) {
				count ++;
			} else if (s.equals("}")) {
				count --;
			}
		}
		
		return count > 0;
	}
	
	public static void main(String[] args) {
		String raw_output = "/home/troy/research/BOA/Maple/example/StringTokenizer.nextToken/small-sequence.txt";
		String seq = "/home/troy/research/BOA/Maple/example/StringTokenizer.nextToken/small-output.txt";
		HashSet<HashSet<String>> queries = new HashSet<HashSet<String>>();
		HashSet<String> q1 = new HashSet<String>();
		q1.add("nextToken");
		queries.add(q1);
		HashMap<ArrayList<APISeqItem>, Integer> patterns = PatternMiner.mine(raw_output, seq, queries, 0.6, 74);
		for(ArrayList<APISeqItem> sp : patterns.keySet()) {
			System.out.println(sp + ":" + patterns.get(sp));
		}
	}
}
