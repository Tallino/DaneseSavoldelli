
--------SIGNATURES--------
sig User {
	telephone: one Int,	
	id: one Int
}

sig Authority{
	dbp: one Int,
	id: one Int
}

sig Violation {
	id: one Int,
	us: one User,
}

sig Report {
	violation: one Violation,
	priority: one Int,
	elapsedDays: one Int,
	coordinates: one Int
} {
	priority > 0
}

sig Database {	
	-- Queued: it represents the set of unverified 
	-- reports that come from users

	-- Confirmed: it represents the set of Reports that
	-- have been checked from the authority. 

	queued: set Report,
	confirmed: set Report,
	suggestions: set Suggestion
} {
	-- The cardinality of queued set is greater or equal to
	-- the one of confimed because reports can be discarded

	#queued >= #confirmed
}

sig UserDatabase {
	users: set User
}

sig AuthorityDatabase {
	authorities: set Authority
}

sig Suggestion {
	id: one Int,
	coordinates: one Int
}


------------------FACTS-------------------

fact NoEqualReports {
	
	---- There can't be two duplicate Reports in the database
	no disjoint r1, r2: Report, db: Database |
(r1 in db.queued and r2 in db.queued)
		iff
(r1.violation.id != r2.violation.id)

}

fact NoEqualTelephones{

	--if two telephones
	--are equal, then it must be
	-- the same user
	no disjoint u1, u2: User |
		
	(u1.telephone = u2.telephone) 
iff
	(u1.id = u2.id)
}


fact NoEqualDbp{
	-- if two dbp
	-- are equal, then it must be
	-- the same authority and vice versa
	no disjoint a1, a2: Authority |	
	(a1.dbp = a2.dbp) 
iff
	(a1.id = a2.id)
}

fact AuthorityExistance {
	
	-- if an authority is registered then
	-- he must be in the authority database

	no disjoint a: Authority, db: AuthorityDatabase |
	(a in db.authorities) iff (a.id>0)
}
	

fact UserExistance {
	
	--if a user is registered then
	--he must be in the user database

	no disjoint u: User, db: UserDatabase |
	(u in db.users) iff (u.id>0)
}

fact SuggestionExistance {

	--if a suggestion is raised then
	--he must be in the suggestion database

	no disjoint s: Suggestion, db: Database |
	(s in db.suggestions) iff (s.id>0)
}

fact DisjointQueuedAndConfirmed {

	-- A report cannot be both in confirmed and
	-- queued sets at the same time.

	no disjoint r: Report, db: Database | 
		r in db.queued iff r not in db.confirmed
}



fact NoSuggestionIfNoReports {

	-- If queued does not contain any reports of
	-- violations occurred in a specified location
	-- then Suggestion of that location must not be raised.

	all r: Report, s: Suggestion | one db: Database | 
		(r.coordinates = s.coordinates and r in db.queued) iff
(s in db.suggestions)

}	


---------------ASSERTIONS------------

assert UniquenessOfReports{
	

	all r1, r2: Report, db: Database |

not (	r1.violation.id = r2.violation.id		)
		
implies not

(	r1 in db.queued and r2 in db.queued	)	

}

check UniquenessOfReports 

	
assert UniqueTelephones {

		all u1,u2: User |
not	(u1.telephone=u2.telephone)

implies
	(u1.id = u2.id)
}

check UniqueTelephones

assert UniqueDBP{
	all a1, a2: Authority |	
	not (a1.id = a2.id) 
implies
(a1.dbp = a2.dbp) 

}

check UniqueDBP

assert DisjointedQueues {

	no disjoint r: Report, db: Database | 
 not (r in db.confirmed)
iff (r in db.queued)
}

check DisjointedQueues

--------------------PREDICATES---------------------

pred show() {
#Violation > 1
#Report > 1
#Suggestion > 1
#User > 1
#Authority > 1
#Database > 1
#UserDatabase > 1
#AuthorityDatabase > 1
}

run show for 2


