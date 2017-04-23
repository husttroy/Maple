package edu.ucla.cs.search;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import edu.ucla.cs.main.Utils;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.Answer;
import edu.ucla.cs.parse.APITypeVisitor;
import edu.ucla.cs.parse.PartialProgramAnalyzer;

public class Search {
	public HashSet<Answer> search(HashSet<String> typeQuery, HashSet<ArrayList<String>> apiQueries) {
		MySQLAccess access = new MySQLAccess();
		access.connect();
		HashSet<HashSet<String>> keywords = new HashSet<HashSet<String>>();
		for(ArrayList<String> apiQuery : apiQueries) {
			HashSet<String> keyword = new HashSet<String>();
			ArrayList<String> apiNames = new ArrayList<String>();
			for(String api : apiQuery) {
				apiNames.add(api.substring(0, api.indexOf('(')));
			}
			keyword.addAll(typeQuery);
			keyword.addAll(apiNames);
			keywords.add(keyword);
		}
		
		HashSet<Answer> answers = access.searchCodeSnippets(keywords);
		access.close();
		
		Iterator<Answer> iter1 = answers.iterator();
		while(iter1.hasNext()) {
			Answer answer = iter1.next();
//			if(answer.id == 6896319) {
//				System.out.println();
//			}
			String content = answer.body;
			ArrayList<String> snippets = getCode(content);
			Iterator<String> iter2 = snippets.iterator();
			boolean flag1 = false; // this flag indicates whether this SO post contains a satisfiable snippet
			while(iter2.hasNext()) {
				String snippet = iter2.next();
				// coarse-grained filtering by checking whether it is just a single code term
				if(!snippet.contains(System.lineSeparator()) && !snippet.contains(";")) {
					iter2.remove();
					continue;
				}
				
				// coarse-grained filtering by checking whether the snippet contains keywords from one of the queries
				boolean flag2 = true; // this flag indicates whether this snippet satisfies the coarse-grained filtering criteria
				for(HashSet<String> query : keywords) {
					for(String keyword : query) {
						if(!snippet.contains(keyword)) {
							flag2 = false;
							break;
						}
					}
					
					if(flag2) {
						break;
					}
				}
				
				if(!flag2) {
					iter2.remove();
					continue;
				}
				
				// fine-grained filtering by parsing the code snippet to check for ambiguous names
				PartialProgramAnalyzer analyzer;
				HashMap<String, ArrayList<APISeqItem>> seqs = null;
				try {
					analyzer = new PartialProgramAnalyzer(snippet);
					answer.containsIncompleteSnippet = analyzer.isIncomplete;
					seqs = analyzer.retrieveAPICallSequences();
				} catch (Exception e) {
					// parse error
					iter2.remove();
					continue;
				}
				
				if(seqs == null) {
					iter2.remove();
					continue;
				} else {
					boolean flag3 = false;  // this flag indicates whether this snippet contains a method that satisfies the fine-grained filtering criteria
					for(String method : seqs.keySet()) {
//						if(!method.equals("onCreate")) {
//							continue;
//						}
						ArrayList<APISeqItem> seq = seqs.get(method);
						
						// check whether the API call sequences contain all queried APIs in the same order
						ArrayList<String> calls = new ArrayList<String>();
						for(APISeqItem item : seq) {
							if(item instanceof APICall) {
								APICall call = (APICall)item;
								calls.add(call.name);
							}
						}
						
						// remove the snippet if it does not contain the APIs in the same order in any of the input queries
						boolean flag = false;
						for(ArrayList<String> apis : apiQueries) {
							if(Utils.isSubsequence(calls, apis)) {
								flag = true;
								break;
							} 
						}
						
						if(!flag) {
							continue;
						} else {
							if(!typeQuery.isEmpty()) {
								// additional check on types to handle ambiguous API calls
								APITypeVisitor tv = analyzer.resolveTypes();
								HashSet<String> ts = tv.types;
								HashMap<String, String> tm = tv.map;
								if(!ts.containsAll(typeQuery)) {
									continue;
								} else {
									boolean flag4 = true; // this flag indicates whether the matched API calls in this method are the API calls with the same queried type
									// further check the receiver type of each searched API call to ensure it is the same API
									for(APISeqItem item : seq) {
										if(item instanceof APICall) {
											APICall call = (APICall)item;
											for(ArrayList<String> apis: apiQueries) {
												if(apis.contains(call.name)) {
													// look up the map to resolve the type of its receiver
													if(tm.containsKey(call.receiver) && typeQuery.contains(tm.get(call.receiver))) {
														// yes the receiver has the searched type
														continue;
													} else {
														flag4 = false;
														break;
													}
												}
											}
										}
									}
									
									if(flag4) {
										answer.seq.put(snippet, seq);
										flag1 = true;
										flag3 = true;
									}
								}
							} else {
								answer.seq.put(snippet, seq);
								flag1 = true;
								flag3 = true;
							}
						}
					}
					
					if(!flag3) {
						// the code snippet does not contain any of queried keywords, remove it
						iter2.remove();
					}
				}
			}
			
			if(!flag1) {
				// no code snippet in the post is satisfied, remove this post
				iter1.remove();
			}
		}
		
		return answers;
	}
	
	private static ArrayList<String> getCode(String body) {
		ArrayList<String> codes = new ArrayList<>();
		String start = "<code>", end = "</code>";
		int s = 0;
		while (true) {
			s = body.indexOf(start, s);
			if (s == -1)
				break;
			s += start.length();
			int e = body.indexOf(end, s);
			if (e == -1)
				break;
			codes.add(body.substring(s, e).trim());
			s = e + end.length();
		}
		return codes;
	}
}
