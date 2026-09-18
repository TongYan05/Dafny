datatype date = Date(day:nat, month:nat, year:nat)

function makeFirstOfJan(d : date) : date
{
  d.(day := 1, month := 1)
}

// what about a day-after function?