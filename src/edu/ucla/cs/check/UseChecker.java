package edu.ucla.cs.check;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import edu.ucla.cs.mine.PredicatePatternMiner;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.Answer;
import edu.ucla.cs.model.ControlConstruct;
import edu.ucla.cs.model.MethodCall;
import edu.ucla.cs.model.Violation;
import edu.ucla.cs.model.ViolationType;
import edu.ucla.cs.utils.SAT;

public class UseChecker {
	
	private ArrayList<APISeqItem> common;
	
	public UseChecker() {
		this.common = new ArrayList<APISeqItem>();
	}
	
	public HashMap<Answer, ArrayList<Violation>> check(
			ArrayList<APISeqItem> pattern, ArrayList<Answer> answers) {
		HashMap<Answer, ArrayList<Violation>> violations = new HashMap<Answer, ArrayList<Violation>>();
		for (Answer answer : answers) {
			for (ArrayList<APISeqItem> seq : answer.seq.values()) {
				ArrayList<Violation> vios = validate(pattern, seq);
				if(!vios.isEmpty()) {
					ArrayList<Violation> value;
					if(violations.containsKey(answer)) {
						value = violations.get(answer);
					} else {
						value = new ArrayList<Violation>();
					}
					value.addAll(vios);
					violations.put(answer, value);
					answer.buggy_seq_count++;
				}
				
				// reset
				common.clear();
			}
		}
		return violations;
	}

	/**
	 * 
	 * Check whether the sequence violates the pattern If it does, characterize
	 * the violations. 1. Exception Handling 2. Error Handling 3. Weakest
	 * Precondition 4. API Call Ordering 5. API Call Completeness 6. Alternative
	 * Use (*)
	 * 
	 * @param pattern
	 * @param seq
	 * @return
	 */
	private ArrayList<Violation> validate(ArrayList<APISeqItem> pattern,
			ArrayList<APISeqItem> seq) {
		ArrayList<Violation> violations = new ArrayList<Violation>();

		// compute the longest common subseqeunce
		ArrayList<APISeqItem> lcs = LCS(pattern, seq);
		
		for(APISeqItem item : pattern) {
			if(item instanceof ControlConstruct) {
				if(!lcs.contains(item) && !seq.contains(item)) {
					violations.add(new Violation(ViolationType.MissingStructure, item));
					continue;
				} else if (!lcs.contains(item) && seq.contains(item)) {
					violations.add(new Violation(ViolationType.DisorderStructure, item));
				}
			} else {
				APICall call1 = (APICall)item;
				APICall call2 = null;
				// find the corresponding call2, if any
				if(lcs.contains(call1)) {
					int index = lcs.indexOf(call1);
					call2 = (APICall)common.get(index);
				} else {
					// try to find in the sequence
					for(APISeqItem a : seq) {
						if(a instanceof APICall && ((APICall)a).name.equals(call1.name)) {
							call2 = (APICall)a;
							violations.add(new Violation(ViolationType.DisorderMethodCall, call2));
							break;
						}
					}
				}
				
				if(call2 == null) {
					violations.add(new Violation(ViolationType.MissingMethodCall, item));
				} else {
					// check whether the precondition of API call in pattern is implied by the precondition of the API call in the sequence
					SAT sat = new SAT();
					// condition and normalize the path condition of api2
					HashSet<String> relevant_element = new HashSet<String>();
					ArrayList<String> rcv = new ArrayList<String>();
					ArrayList<ArrayList<String>> args = new ArrayList<ArrayList<String>>();
					if (call2.receiver != null) {
						relevant_element.add(call2.receiver);
						rcv.add(call2.receiver);
					}
					relevant_element.addAll(call2.arguments);
					args.add(call2.arguments);
					String cond = PredicatePatternMiner.condition(
							relevant_element, call2.condition);
					cond = PredicatePatternMiner.normalize(cond, rcv, args);
					if (!sat.checkImplication(cond, call1.condition)) {
						// precondition violation
						Violation vio = new Violation(
								ViolationType.IncorrectPrecondition, call2);
						violations.add(vio);
					}
				}
			}
		}

		return violations;
	}
	
	public ArrayList<APISeqItem> LCS(ArrayList<APISeqItem> seq1, ArrayList<APISeqItem> seq2) {
	    int[][] lengths = new int[seq1.size()+1][seq2.size()+1];
	    
	    for (int i = 0; i < seq1.size(); i++) {
	    	APISeqItem item1 = seq1.get(i);
	        for (int j = 0; j < seq2.size(); j++) {
	        	APISeqItem item2 = seq2.get(j);
	        	if(item1.getClass().equals(item2.getClass())) {
	        		if (item1 instanceof APICall) {
	        			APICall call1 = (APICall)item1;
	        			APICall call2 = (APICall)item2;
	        			if(call1.name.equals(call2.name)) {
	        				lengths[i+1][j+1] = lengths[i][j] + 1;
	        			} else {
	        				lengths[i+1][j+1] =
	        	                    Math.max(lengths[i+1][j], lengths[i][j+1]);
	        			}
	        		} else {
	        			ControlConstruct construct1 = (ControlConstruct)item1;
	        			ControlConstruct construct2 = (ControlConstruct)item2;
	        			if(construct1.equals(construct2)) {
	        				lengths[i+1][j+1] = lengths[i][j] + 1;
	        			} else {
	        				lengths[i+1][j+1] =
	        	                    Math.max(lengths[i+1][j], lengths[i][j+1]);
	        			}
	        		}
	        	} else {
	        		lengths[i+1][j+1] =
		                    Math.max(lengths[i+1][j], lengths[i][j+1]);
	        	}   
	        }
	    }
	    
		ArrayList<APISeqItem> lcs = new ArrayList<APISeqItem>();
		for (int x = seq1.size(), y = seq2.size(); x != 0 && y != 0; ) {
	        if (lengths[x][y] == lengths[x-1][y])
	            x--;
	        else if (lengths[x][y] == lengths[x][y-1])
	            y--;
	        else {
	            lcs.add(seq1.get(x-1));
	            common.add(seq2.get(y-1));
	            x--;
	            y--;
	        }
		}
		
		return lcs;
	}
}
