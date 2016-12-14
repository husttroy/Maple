package edu.ucla.cs.process;

import com.google.common.collect.HashMultiset;

import edu.ucla.cs.model.Assignment;
import edu.ucla.cs.model.Method;

public class AssignmentProcessor extends ProcessStrategy{

	@Override
	void process(String line) {
		Method m = getMethodInstance(line);
		buildArgumentMap(m, line);
	}

	protected void buildArgumentMap(Method m, String line) {
		String s = line.substring(line.indexOf("] =") + 3).trim();
		String[] ss = s.split("@@");
		for(int i = 0; i < ss.length; i++){
			String lhs = ss[i].split("->")[0];
			String rs = ss[i].split("->")[1];
			
			HashMultiset<Assignment> as = HashMultiset.create();
			
			String[] arr = rs.split(";;;");
			for(int j = 0; j < arr.length; j++) {
				String rhs = arr[j];
				Assignment assign = new Assignment(lhs, rhs);
				as.add(assign);
			}
			
			m.assigns.put(lhs, as);
		}
	}
}
