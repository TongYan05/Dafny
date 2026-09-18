datatype month = 
  Jan | Feb | Mar | Apr | May | Jun | 
  Jul | Aug | Sep | Oct | Nov | Dec

/* 30 days hath April, June, September and November, 
   All the rest have 31, save Februrary alone ... */
function monthLen(m:month) : nat
{
    match m {
    case Jan | Mar | May | Jul | Aug | Oct | Dec => 31
    case Apr | Jun | Sep | Nov => 30
    case Feb => 28
    }
}

// let's get this right for leap-years