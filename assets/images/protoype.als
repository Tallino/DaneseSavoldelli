
--------SIGNATURES--------

sig User {
email: one String,
telephone: one Int,
password: one String,
id: one Int
}

sig Authority{
auc: one String,
dbp: one Int,
id: one Int
}

sig Violation {
	id: one Int,
	plate: one String,
	time: one String,
	location: one String,
}

sig Report {
	violation: one Violation,
	priority: one Int,
	elapsedDays: one Int
} {
	priority > 0
}

sig Database {
	queued: set Report,
	confirmed: set Report
}

sig UserDatabase {
	users: set User
}

sig AuthorityDatabase {
	authorities: set Authority
}


------------------FACTS-------------------
fact NoDifferentViolations {
	
	-- if two violations have occurred
	-- on the same location in the same time and 
	-- belong to the same plate then they must have 
	-- the same id and vice versa.

	one v1, v2: Violation |
		(
			v1.plate = v2.plate and
			v1.time = v2.time and
			v1.location = v2.location
		) iff 
		(
			v1.id = v2.id
		)
}

fact NoDifferentEmailsOrTelephone{

	--if two emails or two telephones
	--are equal, then it must be
	-- the same user

	one u1, u2: User |
		
	(
		u1.email = u2.email or
		u1.telephone = u2.telephone
	) iff
	(
		u1.id = u2.id
	)
}


fact NoDifferentAucOrDbp{

	--if two auc or two dbp
	--are equal, then it must be
	-- the same authority

	one a1, a2: Authority |	
	(
		a1.auc = a2.auc or
		a1.dbp = a2.dbp
	) iff
	(
		a1.id = a2.id
	)
}


fact AuthorityExistance {
	
--	if an authority is registered then
	--he must be in the authority database

	one a:Authority |
(a in Authority) iff (a.id>0)
}
	

fact UserExistance {
	
	--if a user is registered then
	--he must be in the user database

	one u:User |
	(u in User) iff (u.id>0)
}	


---------------ASSERTIONS------------


assert NoDuplicatedReports {

	-- All different reports in queued or confirmed 
	-- inboxes must have different related violations

	one db: Database |
			(
				all r1, r2: Report |
					r1 in db.queued and r2 in db.queued and
					r1.violation.id != r2.violation.id and
					r1 != r2
			)
		and
			(	
				all r1, r2: Report |
					r1 in db.confirmed and r2 in db.confirmed and
					r1.violation.id != r2.violation.id and
					r1 != r2
			)
}

check NoDuplicatedReports for 10

assert NoMoreThan7Days {

	--any report which have been queued for
	-- more than 7 days expires

	all r: Report, d: Database |
	(r.elapsedDays >= 7) implies (r not in d.queued)
}

check NoMoreThan7Days
	
assert PriorityIncrease {
	--if the same violation is being reported more than once
	--then its priority increases

		all r1,r2: Report, d: Database |
	(r1 in d.queued and r2 in d.queued and r1.id = r2.id) implies
	(r1.priority > r2.priority)
}

check PriorityIncrease




--------------------PREDICATES---------------------


pred createUser[u: User, em: String, tel: Int, pass: String, i: Int] {
	u.email = em
	u.telephone = tel
	u.password = pass
	u.id = i
}

pred createAuth[a: Authority, au: String, dev: Int, i: Int] {
		
	a.auc=au
	a.dbp=dev
	a.id=i
}

