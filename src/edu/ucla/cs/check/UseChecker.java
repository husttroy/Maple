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
//	public static HashMap<Answer, ArrayList<Violation>> check(
	public static HashSet<Answer> check(
			ArrayList<APISeqItem> pattern, ArrayList<Answer> answers) {
//		HashMap<Answer, ArrayList<Violation>> violations = new HashMap<Answer, ArrayList<Violation>>();
		HashSet<Answer> violations = new HashSet<Answer>();
		for (Answer answer : answers) {
			for (ArrayList<APISeqItem> seq : answer.seq.values()) {
//				ArrayList<Violation> vios = validate(pattern, seq);
//				if(!vios.isEmpty()) {
//					violations.put(answer, vios);
//				}
				if(validate(pattern, seq)) {
					violations.add(answer);
				}
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
	private static boolean validate(ArrayList<APISeqItem> pattern,
			ArrayList<APISeqItem> seq) {
//		ArrayList<Violation> violations = new ArrayList<Violation>();

		// compute the longest common subseqeunce
		ArrayList<APISeqItem> lcs = LCS(pattern, seq);
		
		if(lcs.size() != pattern.size()) return true;
		else return false;
		
//		ArrayList<APISeqItem> copy = new ArrayList<APISeqItem>(pattern);
//		Iterator<APISeqItem> iter1 = copy.iterator();
//		Iterator<APISeqItem> iter2 = seq.iterator();
//		APISeqItem item1 = iter1.next();
//		APISeqItem item2 = iter2.next();
//		while (true) {
//			if (item1 instanceof APICall && item2 instanceof APICall) {
//				APICall api1 = (APICall) item1;
//				APICall api2 = (APICall) item2;
//				if (api1.name.equals(api2.name)) {
//					// same API call, remove the item from copy of the pattern
//					iter1.remove();
//
//					// check whether the path condition of api2 implies the
//					// weakest precondition in api1
//					SAT sat = new SAT();
//					// condition and normalize the path condition of api2
//					HashSet<String> relevant_element = new HashSet<String>();
//					ArrayList<String> rcv = new ArrayList<String>();
//					ArrayList<ArrayList<String>> args = new ArrayList<ArrayList<String>>();
//					if (api2.receiver != null) {
//						relevant_element.add(api2.receiver);
//						rcv.add(api2.receiver);
//					}
//					relevant_element.addAll(api2.arguments);
//					args.add(api2.arguments);
//					String cond = PredicatePatternMiner.condition(
//							relevant_element, api2.condition);
//					cond = PredicatePatternMiner.normalize(cond, rcv, args);
//					if (!sat.checkImplication(cond, api1.condition)) {
//						// precondition violation
//						Violation vio = new Violation(
//								ViolationType.IncorrectPrecondition, api2);
//						violations.add(vio);
//					}
//
//					if (!iter1.hasNext() || !iter2.hasNext()) {
//						break;
//					} else {
//						// move both iterators forward
//						item1 = iter1.next();
//						item2 = iter2.next();
//					}
//					
//				} else {
//					// different API calls
//					if (!iter2.hasNext()) {
//						break;
//					} else {
//						// move iter2 one step forward
//						item2 = iter2.next();
//					}
//				}
//			} else if(item1 instanceof ControlConstruct && item2 instanceof ControlConstruct) {
//				if(item1.equals(item2)) {
//					// same control-flow construct
//					iter1.remove();
//					
//					if (!iter1.hasNext() || !iter2.hasNext()) {
//						break;
//					} else {
//						// move both iterators forward
//						item1 = iter1.next();
//						item2 = iter2.next();
//					}
//				} else {
//					// different control-flow construct
//					if (!iter2.hasNext()) {
//						break;
//					} else {
//						// move iter2 one step forward
//						item2 = iter2.next();
//					}
//				}
//			} else {
//				// different types of items
//				if (!iter2.hasNext()) {
//					break;
//				} else {
//					// move iter2 one step forward
//					item2 = iter2.next();
//				}
//			}
//		}
//
//		if (!copy.isEmpty()) {
//			// some API calls are missing or incorrectly ordered
//			for(APISeqItem item : copy) {
//				if(item instanceof MethodCall) {
//					Violation vio;
//					if(contains(seq, item)) {
//						vio = new Violation(ViolationType.MisorderMethodCall, item);
//					} else {
//						vio = new Violation(ViolationType.MissingMethodCall, item);
//					}
//					
//					violations.add(vio);
//				} else if (item instanceof ControlConstruct) {
//					Violation vio;
//					if(contains(seq, item)) {
//						vio = new Violation(ViolationType.MisorderStructure, item);
//					} else {
//						vio = new Violation(ViolationType.MissingStructure, item);
//					}
//					
//					violations.add(vio);
//				}
//			}
//		}

//		return violations;
	}
	
	private static boolean contains(ArrayList<APISeqItem> arr, APISeqItem item) {
		for(APISeqItem i : arr) {
			if(i instanceof APICall && item instanceof APICall) {
				APICall call1 = (APICall)i;
				APICall call2 = (APICall)item;
				if(call1.name.equals(call2.name)) {
					return true;
				}
			} else if (i instanceof ControlConstruct && item instanceof ControlConstruct) {
				if(i.equals(item)) {
					return true;
				}
			}
		}
		
		return false;
	}
	
	public static ArrayList<APISeqItem> LCS(ArrayList<APISeqItem> seq1, ArrayList<APISeqItem> seq2) {
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
//	            assert a.charAt(x-1) == b.charAt(y-1);
	            lcs.add(seq1.get(x-1));
	            x--;
	            y--;
	        }
		}
		
		return lcs;
	}
}
