package edu.ucla.cs.model;

import java.util.ArrayList;

public class Assignment {
	String lhs;
	ArrayList<String> rhs;
	
	public Assignment(String var, String expr) {
		this.lhs = var;
		this.rhs = new ArrayList<String>();
		String[] arr = expr.split("|");
		// skip the first element because it is empty
		for(int i = 1; i < arr.length; i++) {
			this.rhs.add(arr[i]);
		}
	}
	
	@Override
	public boolean equals(Object o){
		if (!(o instanceof Assignment)) {
			return false;
		}
		
		Assignment that = (Assignment)o;
		return this.lhs.equals(that.lhs) && this.rhs.equals(that.rhs);
	}
	
	@Override
	public int hashCode() {
		int hash = 1;
		hash = hash + 17 * this.lhs.hashCode();
		hash = hash + 31 * this.rhs.hashCode();
		return hash;
	}
	
	@Override
	public String toString(){
		return this.lhs + "->"+ this.rhs.toString();
	}
}
