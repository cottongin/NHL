###
# Copyright (c) 2017, cottongin
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#   * Redistributions of source code must retain the above copyright notice,
#     this list of conditions, and the following disclaimer.
#   * Redistributions in binary form must reproduce the above copyright notice,
#     this list of conditions, and the following disclaimer in the
#     documentation and/or other materials provided with the distribution.
#   * Neither the name of the author of this software nor the name of
#     contributors to this software may be used to endorse or promote products
#     derived from this software without specific prior written consent.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE
###

###
# Includes contributions from Santiago Gil and Jonathan "grateful" Surman
###

import time
import re
import urllib.request as urlreq
import requests

import datetime
import dateutil.parser
import pytz

import urllib.parse as urlparse
import urllib
import supybot.ircdb as ircdb
import supybot.schedule as schedule
import json
import supybot.registry as registry
import supybot.conf as conf
import supybot.utils as utils
from supybot.commands import *
import supybot.plugins as plugins
import supybot.ircutils as ircutils
import supybot.callbacks as callbacks
import supybot.ircmsgs as ircmsgs
try:
    from supybot.i18n import PluginInternationalization
    _ = PluginInternationalization('NHL')
except ImportError:
    # Placeholder that allows to run the plugin on a bot
    # without the i18n module
     _ = lambda x: x

class NHL(callbacks.Plugin):
    """Plugin provides stats and game summaries for NHL games and players"""
    threaded = True

    def __init__(self, irc):
        self.__parent = super(NHL, self)
        self.__parent.__init__(irc)
        self._SCOREBOARD_ENDPOINT = ("https://statsapi.web.nhl.com/api/v1/schedule?" +
                                     "startDate={}&endDate={}" +
                                     "&expand=schedule.teams,schedule.linescore," + 
                                     "schedule.broadcasts.all,schedule.ticket," + 
                                     "schedule.game.content.media.epg" +
                                     "&leaderCategories=&site=en_nhl&teamId=")
        self._FUZZY_DAYS = ['yesterday', 'tonight', 'today', 'tomorrow']

        # These two variables store the latest data acquired from the server
        # and its modification time. It's a one-element cache.
        # They are used to employ HTTP's 'If-Modified-Since' header and
        # avoid unnecessary downloads for today's information (which will be
        # requested all the time to update the scores).
        self._today_scores_cached_url = None
        self._today_scores_last_modified_time = None
        self._today_scores_last_modified_data = None
        
    def _bold(self, string):
        """Returns a bold string."""
        return ircutils.bold(string)

############################
# Date-manipulation helpers
############################
    def _getTodayDate(self):
        """Get the current date formatted as "YYYYMMDD".
        Because the API separates games by day of start, we will consider and
        return the date in the Pacific timezone.
        The objective is to avoid reading future games anticipatedly when the
        day rolls over at midnight, which would cause us to ignore games
        in progress that may have started on the previous day.
        Taking the west coast time guarantees that the day will advance only
        when the whole continental US is already on that day."""
        today = self._pacificTimeNow().date()
        today_iso = today.isoformat()
        return today_iso #.replace('-', '')

    def _easternTimeNow(self):
        return datetime.datetime.now(pytz.timezone('US/Eastern'))

    def _pacificTimeNow(self):
        return datetime.datetime.now(pytz.timezone('US/Pacific'))

    def _ISODateToEasternTime(self, iso):
        """Convert the ISO date in UTC time that the API outputs into an
        Eastern time formatted with am/pm. (The default human-readable format
        for the listing of games)."""
        date = dateutil.parser.parse(iso)
        date_eastern = date.astimezone(pytz.timezone('US/Eastern'))
        eastern_time = date_eastern.strftime('%A %-I:%M %p')
        return "{} ET".format(eastern_time) # Strip the seconds

    def _stripDateSeparators(self, date_string):
        return date_string.replace('-', '')

    def _EnglishDateToDate(self, date):
        """Convert a human-readable like 'yesterday' to a datetime object
        and return a 'YYYYMMDD' string."""
        if date == "lastweek":
            day_delta = -7
        elif date == "yesterday":
            day_delta = -1
        elif date == "today" or date =="tonight":
            day_delta = 0
        elif date == "tomorrow":
            day_delta = 1
        elif date == "nextweek":
            day_delta = 7
        # Calculate the day difference and return a string
        date_string = (self._pacificTimeNow() +
                      datetime.timedelta(days=day_delta)).strftime('%Y-%m-%d')
        return date_string

    def _checkDateInput(self, date):
        """Verify that the given string is a valid date formatted as
        YYYY-MM-DD. Also, the API seems to go back until 2014-10-04, so we
        will check that the input is not a date earlier than that."""
        if date is None:
            return None

        if date in self._FUZZY_DAYS:
            date = self._EnglishDateToDate(date)
        elif date.replace('-','').isdigit():
            try:
                parsed_date = datetime.datetime.strptime(date, '%Y-%m-%d')
            except:
                raise ValueError('Incorrect date format, should be YYYY-MM-DD')

        else:
            return None

        return date

    def _goalSummary(self, data):
        """ parses goals """

        # get all scoring plays
        scores = []
        for item in data['liveData']['plays']['allPlays']:
            if item['result']['eventTypeId'] == 'GOAL':
                scores.append(item)

        # parse scoring plays into relevant data
        scores_list = []
        for item in scores:
            names = []
            for player in item['players']:
                # we don't care about the goalie
                if 'Goalie' not in player['playerType']:
                    name = player['player']['fullName']
                    # if the player is the goal scorer, add the number of goals
                    # he has on the year
                    if 'Scorer' in player['playerType']:
                        num = '(' + str(player['seasonTotal']) + ')'
                    else:
                        num = ''
                    # parse their name
                    fname = name[0] + '.'
                    if len(name.split()) > 2:
                        fname += name.split()[1:-1][0] + ' '
                    lname = name.split()[-1]
                    pname = fname + lname + num
                    # append their name to the names list
                    names.append(pname)
            # parse if it's a special goal or not
            if 'PPG' in item['result']['strength']['code']:
                GT = ' PP'
            elif 'SHG' in item['result']['strength']['code']:
                GT = ' SH'
            else:
                GT = ''
            # parse time and add PP
            time = ('[' + item['about']['ordinalNum'] +
                    '/' + item['about']['periodTime'] + GT +
                    ']')
            # append the team, time, and names to the scores list
            scores_list.append([item['team']['triCode'], time, names])

        # parse the scores list and format to reply
        reply = []
        for item in scores_list:
            # if more than one player there were assists, put those in ()
            if len(item[2]) > 1:
                reply_names = '{} ({})'.format(self._bold(item[2][0]),
                                               ', '.join(name for name in item[2][1:]))
            else:
                reply_names = '{}'.format(self._bold(item[2][0]))
            reply.append('{0} {2} {1}'.format(self._bold(item[0]), item[1], reply_names))

        if len(reply) > 5:
            goals_string = []
            goals_string.append(' | '.join(item for item in reply[:5]))
            goals_string.append(' | '.join(item for item in reply[5:]))
        else:
            goals_string = ' | '.join(item for item in reply)

        return goals_string

    def _findGamepk(self, args):

        num_args = len(args.split())
        if num_args > 2:
            return 'too many args'
        elif num_args == 2:
            # got team and date
            optional_team = args.split()[0]
            optional_date = args.split()[1]
        elif num_args == 1:
            # got team
            optional_team = args
        else:
            pass
            # someone's an idiot

        if optional_team is None:
            team = "all"
            try:
                date = self._checkDateInput(optional_date)
            except ValueError as e:
                print('ERROR: {0!s}'.format(e))
                return
        else:
            date = self._checkDateInput(optional_team)
            if date:
                team = "all"
            else:
                team = optional_team.upper()
                try:
                    date = self._checkDateInput(optional_date)
                except ValueError as e:
                    print('ERROR: {0!s}'.format(e))
                    return

        if date is None:
            games = self._getTodayGames(team)
        else:
            games = self._getGamesForDate(team, date)
        return games

    def _getTodayGames(self, team):
        games = self._getGames(team, self._getTodayDate())
        return games

    def _getGamesForDate(self, team, date):
        games = self._getGames(team, date)
        return games

    def _getGames(self, team, date):
        """Given a date, populate the url with it and try to download its
        content. If successful, parse the JSON data and extract the relevant
        fields for each game. Returns a list of games."""
        url = self._getEndpointURL(date)

        # (If asking for today's results, enable the 'If-Mod.-Since' flag)
        use_cache = (date == self._getTodayDate())
        response = self._getURL(url, use_cache)

        json = self._extractJSON(response)
        games = self._parseGames(json, team)
        return games

    def _getEndpointURL(self, date):
        return self._SCOREBOARD_ENDPOINT.format(date, date)

    def _getURL(self, url, use_cache=False):
        """Use urllib to download the URL's content. The use_cache flag enables
        the use of the one-element cache, which will be reserved for today's
        games URL. (In the future we could implement a real cache with TTLs)."""
        user_agent = 'Mozilla/5.0 \
                      (X11; Ubuntu; Linux x86_64; rv:45.0) \
                      Gecko/20100101 Firefox/45.0'
        header = {'User-Agent': user_agent}

        # ('If-Modified-Since' to avoid unnecessary downloads.)
        if use_cache and self._haveCachedData(url):
            header['If-Modified-Since'] = self._today_scores_last_modified_time

        request = urllib.request.Request(url, headers=header)

        try:
            response = urllib.request.urlopen(request)
        except urllib.error.HTTPError as error:
            if use_cache and error.code == 304: # Cache hit
                self.log.info("{} - 304"
                              "(Last-Modified: "
                              "{})".format(url, self._cachedDataLastModified()))
                return self._cachedData()
            else:
                self.log.error("HTTP Error ({}): {}".format(url, error.code))
                pass

        self.log.info("{} - 200".format(url))

        if not use_cache:
            return response.read()

        # Updating the cached data:
        self._updateCache(url, response)
        return self._cachedData()

    def _extractJSON(self, body):
        return json.loads(body.decode('utf-8'))

    def _parseGames(self, json, team):
        """Extract all relevant fields from NHL.com's json
        and return a list of games."""
        games = []
        if team.upper() == "GNJD":
            team = 'NJD'
        if json['totalGames'] == 0:
            return games
        for g in json['dates'][0]['games']:
            if team in g['teams']['home']['team']['abbreviation'] or team in g['teams']['away']['team']['abbreviation']:
                gamepk = str(g['gamePk'])
        return gamepk

    def _cachedData(self):
        return self._today_scores_last_modified_data

    def _haveCachedData(self, url):
        return (self._today_scores_cached_url == url) and \
                (self._today_scores_last_modified_time is not None)

    def _cachedDataLastModified(self):
        return self._today_scores_last_modified_time

    def _updateCache(self, url, response):
        self._today_scores_cached_url = url
        self._today_scores_last_modified_time = response.headers['last-modified']
        self._today_scores_last_modified_data = response.read()

    # TBD add args for round results
    @wrap
    def nhlplayoffs(self, irc, msg, args):
        """
        Returns NHL playoff results for current round
        """

        # TBD switch out season=YYYYYYYY automatically
        url = ("https://statsapi.web.nhl.com/api/v1/tournaments/playoffs" + 
              "?expand=round.series&season=20162017&site=en_nhl")

        # Fetch content
        content = requests.get(url)
        content_json = json.loads(content.text)
        # Get rounds
        current_round = content_json["defaultRound"]
        round_index = current_round - 1
        round_info = content_json["rounds"][round_index]

        round_name = round_info["names"]["name"]

        # Parse relevant info out of JSON
        padding = 0
        matchups = []
        for item in round_info["series"]:
            record = item["currentGame"]["seriesSummary"]["seriesStatus"]
            matchups.append({
                "name": item["names"]["matchupShortName"],
                "record": record,
                "next": self._ISODateToEasternTime(
                    item["currentGame"]["seriesSummary"]["gameTime"])})
            # Find longest string
            padding = len(record) if len(record) > padding else padding

        # Output
        irc.reply(round_name)
        for item in matchups:
            irc.reply('{0} | {1:{width}} | {2}'.format(item["name"], 
                                                       item["record"], 
                                                       item["next"],
                                                       width=str(padding)))

    def summary(self, irc, msg, args, optargs):
        """<team> [<date>]
        Returns NHL Game Summary - team is required and if no date is given uses today
        """

        # Storing VidUrl to eventually get highlights link.
        # vidurl = ("http://statsapi.web.nhl.com/api/v1/schedule?expand=schedule.game.content.media.epg&leaderCategories=&site=en_nhl&gamePk=" + gamepk)

        gamepk = self._findGamepk(optargs)
        url = ("https://statsapi.web.nhl.com/api/v1/game/" + gamepk +"/feed/live")
        content = requests.get(url)
        content_json = json.loads(content.text)
        game = content_json["gameData"]
        live = content_json["liveData"]
        year = gamepk[:4]
        spacer, gameid = gamepk.split(year)
        HTMLurl = "http://www.nhl.com/scores/htmlreports/{}2017/GS{}.HTM".format(year, gameid)
        VIDEOurl = ("http://statsapi.web.nhl.com/api/v1/schedule?expand=schedule.game.content.media.epg&leaderCategories=&site=en_nhl&gamePk=" + gamepk)

        HTMLurl = utils.web.getUrl("http://tinyurl.com/api-create.php?url="+ HTMLurl)
        HTMLcontent = requests.get(HTMLurl)
        VIDcontent = requests.get(VIDEOurl)
        Attendance = re.search("Attendance\s*(\d+,\d+)", HTMLcontent.text, re.S)
        spacer, Attendance = Attendance.group(0).split(" ")
        VIDEOurl = utils.web.getUrl("http://tinyurl.com/api-create.php?url="+ VIDEOurl)

        # Title
        Header = "\x02{} {} {} {} {}\x02 [Att {}] | SOG {}-{} | BK {}-{} | HITS {}-{} | PP {}/{} {}PIMS - PP {}/{} {}PIMS | FO {}-{} | TK {}-{} | GV {}-{}"
        AwayTeam = game["teams"]["away"]["abbreviation"]
        AwayGoals = live["boxscore"]["teams"]["away"]["teamStats"]["teamSkaterStats"]["goals"]
        HomeTeam = game["teams"]["home"]["abbreviation"]
        HomeGoals = live["boxscore"]["teams"]["home"]["teamStats"]["teamSkaterStats"]["goals"]
        Status = game["status"]["detailedState"]
        Arena = game["teams"]["home"]["venue"]["name"]
        Location = game["teams"]["home"]["venue"]["city"]

        # Powerplay Info
        HomePPG = live["boxscore"]["teams"]["home"]["teamStats"]["teamSkaterStats"]["powerPlayGoals"]
        HomePPG = str(HomePPG)
        HomePPG = HomePPG.rstrip('0').rstrip('.')
        AwayPPG = live["boxscore"]["teams"]["away"]["teamStats"]["teamSkaterStats"]["powerPlayGoals"]
        AwayPPG = str(AwayPPG)
        AwayPPG = AwayPPG.rstrip('0').rstrip('.')

        AwayPPO = live["boxscore"]["teams"]["away"]["teamStats"]["teamSkaterStats"]["powerPlayOpportunities"]
        AwayPPO = str(AwayPPO)
        AwayPPO = AwayPPO.rstrip('0').rstrip('.')
        HomePPO = live["boxscore"]["teams"]["home"]["teamStats"]["teamSkaterStats"]["powerPlayOpportunities"]
        HomePPO = str(HomePPO)
        HomePPO = HomePPO.rstrip('0').rstrip('.')

        # Game Stats
        AwayShots = live["boxscore"]["teams"]["away"]["teamStats"]["teamSkaterStats"]["shots"]
        HomeShots = live["boxscore"]["teams"]["home"]["teamStats"]["teamSkaterStats"]["shots"]
        AwayBK = live["boxscore"]["teams"]["away"]["teamStats"]["teamSkaterStats"]["blocked"]
        HomeBK = live["boxscore"]["teams"]["home"]["teamStats"]["teamSkaterStats"]["blocked"]
        AwayHits = live["boxscore"]["teams"]["away"]["teamStats"]["teamSkaterStats"]["hits"]
        HomeHits = live["boxscore"]["teams"]["home"]["teamStats"]["teamSkaterStats"]["hits"]
        AwayPIM = live["boxscore"]["teams"]["away"]["teamStats"]["teamSkaterStats"]["pim"]
        HomePIM = live["boxscore"]["teams"]["home"]["teamStats"]["teamSkaterStats"]["pim"]
        AwayFO = live["boxscore"]["teams"]["away"]["teamStats"]["teamSkaterStats"]["faceOffWinPercentage"]
        HomeFO = live["boxscore"]["teams"]["home"]["teamStats"]["teamSkaterStats"]["faceOffWinPercentage"]
        AwayTake = live["boxscore"]["teams"]["away"]["teamStats"]["teamSkaterStats"]["takeaways"]
        HomeTake = live["boxscore"]["teams"]["home"]["teamStats"]["teamSkaterStats"]["takeaways"]
        AwayGive = live["boxscore"]["teams"]["away"]["teamStats"]["teamSkaterStats"]["giveaways"]
        HomeGive = live["boxscore"]["teams"]["home"]["teamStats"]["teamSkaterStats"]["giveaways"]

        # Goals
        try:
            reply_string = self._goalSummary(content_json)
            if type(reply_string) is list:
                Goals_String = []
                for item in reply_string:
                    Goals_String.append("{}: {}".format(self._bold("Goals"), item))
            else:
                Goals_String = "{}: {}".format(self._bold("Goals"), self._goalSummary(content_json))
        except:
            Goals_String = None

        # Three Stars
        FirstStar = live["decisions"]["firstStar"]["fullName"]
        SecondStar = live["decisions"]["secondStar"]["fullName"]
        ThirdStar = live["decisions"]["thirdStar"]["fullName"]

        # Goalies
        Winner = live["decisions"]["winner"]["fullName"]
        Loser = live["decisions"]["loser"]["fullName"]

        # Refs
        Referees = []
        RefTable = re.search(r"Referee.*?<table.*?>(.*?)<\/table>", HTMLcontent.text, re.S)
        RefList = re.findall(r"<tr.*?>(.*?)<\/tr>", RefTable.group(0), re.S)
        for elem in RefList:
            addref = re.search(r'<td.*?>(.*?)<\/td>', elem)
            addref = re.sub("<.*?>", "", addref.group(0))
            Referees.append(addref)

        Referees = "{}".format(' '.join(Referees))
        Referees = re.sub("#20 Tim Peel", "\x02\0034-!- #20 Tim Peel -!-", Referees)

        # IRC Replies
        irc.reply(Header.format(AwayTeam, AwayGoals, HomeTeam, HomeGoals, Status, Attendance,
                                AwayShots, HomeShots, AwayBK, HomeBK, AwayHits, HomeHits, AwayPPG,
                                AwayPPO, AwayPIM, HomePPG, HomePPO, HomePIM, AwayFO, HomeFO,
                                AwayTake, HomeTake, AwayGive, HomeGive))
        if Goals_String:
            if type(Goals_String) is list:
                for item in Goals_String:
                    irc.reply("{}".format(item))
            else:
                irc.reply("{}".format(Goals_String))
        irc.reply("\x02Three Stars\x02: 1.{} 2.{} 3.{}    [\x02Goalies\x02 W: {} L: {}]".format(FirstStar, SecondStar, ThirdStar, Winner, Loser))
        irc.reply("\x02Referees\x02: {}".format(str(Referees)))
        irc.reply("\x02HTML Report\x02: {} \x02Video Highlights\x02: {}".format(HTMLurl.decode(), VIDEOurl.decode()))

    summary = wrap(summary, (['text']))

Class = NHL

# vim:set shiftwidth=4 softtabstop=4 expandtab textwidth=79: